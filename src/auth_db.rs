use crate::*;

pub const NODE_CAPACITY: usize = 128;
pub const KEY_SIZE: usize = 20;
pub const DIGEST_SIZE: usize = 224 / 8;
pub const NULL_DIGEST: ADigest = [0; DIGEST_SIZE];

pub type AKey = [u8; KEY_SIZE];
pub type ADigest = [u8; DIGEST_SIZE];
pub type Pointer = usize;

pub const MIN_KEY: AKey = [0; KEY_SIZE];
pub const MAX_KEY: AKey = [255; KEY_SIZE];

pub struct TreeWorkSet {
    cache: HashMap<usize, Mutex<Box<AuthTreeInternalNode>>>,
    remove: Vec<usize>,
}

impl TreeWorkSet {
    pub fn new() -> TreeWorkSet {
        TreeWorkSet {
            cache: HashMap::new(),
            remove: Vec::new(),
        }
    }

    pub fn breakup(self) -> (HashMap<usize, Mutex<Box<AuthTreeInternalNode>>>, Vec<usize>) {
        (self.cache, self.remove)
    }

    pub fn extend(&mut self, workset: TreeWorkSet) {
        self.cache.extend(workset.cache);
        self.remove.extend(workset.remove);
    }
}

pub struct TreeCache {
    pub root: Option<usize>,
    pub cache: HashMap<usize, Mutex<Box<AuthTreeInternalNode>>>,
    pub data: HashMap<usize, AuthTreeEntry>,
    pub next_pointer: AtomicUsize,
}

impl TreeCache {
    pub fn new() -> TreeCache {
        TreeCache {
            root: None,
            cache: HashMap::with_capacity(1000),
            data: HashMap::with_capacity(1000),
            next_pointer: AtomicUsize::new(usize::MAX / 2),
        }
    }

    pub fn clear_updated_pointers(&mut self) -> Vec<Pointer> {
        let mut updated = Vec::new();
        for (k, v) in &mut self.cache {
            v.lock().updated = false;
        }
        updated
    }


    pub fn get_updated_pointers(&mut self) -> Vec<Pointer> {
        let mut updated = Vec::new();
        for (k, v) in &mut self.cache {
            if v.lock().updated {
                updated.push(*k);
            }
        }
        updated
    }

    pub fn apply_workset(&mut self, workset: TreeWorkSet) -> Vec<Pointer> {
        let (cache, remove) = workset.breakup();
        for elem in &remove {
            self.cache.remove(&elem);
        }
        self.cache.extend(cache);
        remove
    }

    pub fn next_pointer(&self) -> Pointer {
        let current_pointer = self.next_pointer.fetch_add(1, Ordering::Relaxed);
        current_pointer
    }

    pub fn get(&self, key: &AKey, pointers: &mut Option<Vec<Pointer>>) -> GetPointer {
        if self.root.is_none() {
            return GetPointer::NotFound;
        }

        let mut next_pointer = self.root.unwrap();
        loop {
            if let Some(ptrs) = pointers {
                ptrs.push(next_pointer);
            }

            let next_node = &self.cache[&next_pointer].lock();
            match next_node.get(key) {
                GetPointer::Goto(p) => {
                    next_pointer = p;
                }
                x => return x,
            }
        }
    }

    pub fn update_with_elements(&mut self, update_slice: &[AuthOp]) -> Vec<Pointer> {
        let num_elements = update_slice.len();

        let now = Instant::now();
        // First deal with the case there is no root. Then we just make an empty one.
        let root_pointer = if self.root.is_none() {
            let root = Box::new(AuthTreeInternalNode::empty(true, [MIN_KEY, MAX_KEY]));
            let root_pointer = self.next_pointer();
            self.cache.insert(root_pointer, Mutex::new(root));
            self.root = Some(root_pointer);
            root_pointer
        } else {
            self.root.unwrap()
        };
        let dur = now.elapsed();
        println!(
            "Root Pointer. {}ns\ttotal: {}ms",
            dur.as_nanos() / num_elements as u128,
            dur.as_millis()
        );

        let now = Instant::now();
        // Make some temporary structures.
        let mut returns = Vec::with_capacity(NODE_CAPACITY);
        let mut spare_elements = Vec::with_capacity(NODE_CAPACITY);

        let mut work_set = TreeWorkSet::new();
        self.update_parallel(
            0,
            &mut work_set,
            &mut returns,
            &mut spare_elements,
            root_pointer,
            update_slice,
        );

        let dur = now.elapsed();
        println!(
            "Child Update. {}ns\ttotal: {}ms",
            dur.as_nanos() / num_elements as u128,
            dur.as_millis()
        );

        println!("Node additions: {} Removals: {}", work_set.cache.len(), work_set.remove.len());

        let now = Instant::now();
        let removed = self.apply_workset(work_set);
        loop {

            // Now we reduce the number of returns by constructing the tree
            let number_of_returns = returns.len();

            if number_of_returns == 0 && spare_elements.len() == 0 {
                // All elements were deleted, and none wait to be in a block.
                self.root = None;
                return removed;
            }

            // Save the new nodes in the cache, and add them to the list.
            for mut ret in returns.drain(..) {
                let new_pointer = self.next_pointer();
                let mut new_element = AuthElement {
                    key: ret.bounds[1],
                    digest: [0; DIGEST_SIZE], // FIX (security): compute the hash here.
                    pointer: new_pointer,
                };

                ret.compute_hash(&mut new_element.digest);
                spare_elements.push(new_element);
                self.cache.insert(new_pointer, Mutex::new(ret));

                if number_of_returns == 1 {
                    // This is the new root, save and exit.
                    self.root = Some(new_pointer);

                    let dur = now.elapsed();
                    println!(
                        "Make Root. {}ns\ttotal: {}ms",
                        dur.as_nanos() / num_elements as u128,
                        dur.as_millis()
                    );
                    return removed;
                }
            }

            let new_root = AuthTreeInternalNode::empty(false, [MIN_KEY, MAX_KEY]);

            new_root.split_update(
                &mut returns,
                spare_elements.len(),
                &mut spare_elements[..].iter().peekable(),
            );
            spare_elements.clear();
        }
    }

    pub fn update_parallel(
        &self,
        depth: usize,
        work_set: &mut TreeWorkSet,
        returns: &mut Vec<Box<AuthTreeInternalNode>>,
        spare_elements: &mut Vec<AuthElement>,
        pointer: Pointer,
        given_elements: &[AuthOp],
    ) {

        // println!("Wait for lock {}", pointer);
        let node_guard = self.cache[&pointer].lock();
        let this_node = &node_guard;
        // println!("Got lock {}", pointer);
        let intitial_returns = returns.len();
        let intitial_spare_elements = spare_elements.len();

        // Does not work for a leaf node -- revert to normal update.
        if this_node.leaf {
            let mut iter = given_elements.iter().peekable();
            // We must drop the lock to allow update to re-enter.
            drop(node_guard);
            self.update(
                depth + 1,
                work_set,
                returns,
                spare_elements,
                pointer,
                &mut iter,
            );
            return;
        }

        let this_node_len = this_node.elements;
        let positions: Vec<_> = (0..this_node_len).into_iter().collect();

        let computed: Vec<_> = positions
            .par_iter()
            .map(|i| {
                let mut spare_elements: Vec<AuthElement> = Vec::new();
                let mut returns: Vec<Box<AuthTreeInternalNode>> = Vec::new();
                let mut work_set = TreeWorkSet::new();

                let this_child_ref = this_node.get_by_position(*i);

                // Compute the start position:
                let start_position = if *i > 0 {
                    let prev_child_ref = this_node.get_by_position(i - 1);
                    given_elements[..]
                        .binary_search_by_key(&prev_child_ref.key, |elem| *elem.key())
                        .map(|x| x + 1)
                        .unwrap_or_else(|x| x)
                } else {
                    0
                };

                // Compute the end position:
                let end_position = given_elements[..]
                    .binary_search_by_key(&this_child_ref.key, |elem| *elem.key())
                    .map(|x| x + 1)
                    .unwrap_or_else(|x| x);


                if start_position == end_position {
                    // We do not need to explore in this child, so we simply add the element to the spares list
                    spare_elements.push(*this_child_ref); // FIX (perf): COPY HERE
                    return (returns, spare_elements, work_set);
                }

                // We need to explore down this child
                let child_pointer = this_child_ref.pointer;

                if depth == 0 && this_node_len < NODE_CAPACITY / 2 {
                    // Allow for one more level of parallelism, in case the root is very small.
                    self.update_parallel(
                        depth + 1,
                        &mut work_set,
                        &mut returns,
                        &mut spare_elements,
                        child_pointer,
                        &given_elements[start_position..end_position],
                    );
                }
                else {
                    let mut iter = given_elements[start_position..end_position]
                        .iter()
                        .peekable();
                    drop(this_node);
                    self.update(
                        depth + 1,
                        &mut work_set,
                        &mut returns,
                        &mut spare_elements,
                        child_pointer,
                        &mut iter,
                    );
                }

                // Save the new nodes in the cache, and add them to the list.
                for mut ret in returns.drain(intitial_returns..) {
                    let new_pointer = self.next_pointer();
                    let mut new_element = AuthElement {
                        key: ret.bounds[1],
                        digest: [0; DIGEST_SIZE],
                        pointer: new_pointer,
                    };

                    ret.compute_hash(&mut new_element.digest);
                    spare_elements.push(new_element);
                    work_set.cache.insert(new_pointer, Mutex::new(ret));
                }

                // Now get back the node we were considering
                return (returns, spare_elements, work_set);
            })
            .collect();

        for (rets, spares, wset) in computed.into_iter() {
            returns.extend(rets);
            spare_elements.extend(spares);
            work_set.extend(wset);
        }

        this_node.split_update(
            returns,
            spare_elements.len() - intitial_spare_elements,
            &mut spare_elements[intitial_spare_elements..].iter().peekable(),
        );
        spare_elements.truncate(intitial_spare_elements);
        work_set.remove.push(pointer);
    }

    pub fn update<'x, T>(
        &self,
        depth: usize,
        work_set: &mut TreeWorkSet,
        returns: &mut Vec<Box<AuthTreeInternalNode>>,
        spare_elements: &mut Vec<AuthElement>,
        pointer: Pointer,
        iter: &mut Peekable<T>,
    ) where
        T: Iterator<Item = &'x AuthOp>,
    {
        let mut node_guard = self.cache[&pointer].lock();
        let this_node = &node_guard;
        let intitial_returns = returns.len();
        let intitial_spare_elements = spare_elements.len();

        if this_node.leaf {
            let returns_initial_length = returns.len();
            let spare_initial_length = spare_elements.len();
            this_node.merge_into_leaf(returns, spare_elements, iter);
            assert!(spare_elements.len() == spare_initial_length);

            // We special case updating leaves, since we have lots of them.
            // If as a result of the update we only have a single leaf, then
            // we re-write the given leaf in place. Otherwise we create new
            // (many) blocks, re-balancing the items.
            if returns.len() - returns_initial_length == 1 {
                let mut single_block = returns.pop().unwrap(); // safe due to check
                let mut updated_element = AuthElement {
                    key: single_block.bounds[1],
                    digest: [0; DIGEST_SIZE],
                    pointer: pointer,
                };
                single_block.compute_hash(&mut updated_element.digest);
                spare_elements.push(updated_element);

                // Update the block in-place:
                let write_ref : &mut Box<AuthTreeInternalNode> = &mut node_guard;
                single_block.updated = true;
                *write_ref = single_block;
            }
            else
            {
                work_set.remove.push(pointer);
            }
            return;
        }

        // This is an internal node
        let this_node_len = this_node.elements;
        for i in 0..this_node_len {
            let this_child_ref = this_node.get_by_position(i);

            let peek_next = iter.peek();

            if peek_next.is_none() || !(peek_next.unwrap().key() <= &this_child_ref.key) {
                // We do not need to explore in this child, so we simply add the element to the spares list
                spare_elements.push(*this_child_ref); // FIX (perf): COPY HERE
                continue;
            }

            // We need to explore down this child
            let child_pointer = this_child_ref.pointer;

            self.update(
                depth + 1,
                work_set,
                returns,
                spare_elements,
                child_pointer,
                iter,
            );

            // Save the new nodes in the cache, and add them to the list.
            for mut ret in returns.drain(intitial_returns..) {
                let new_pointer = self.next_pointer();
                let mut new_element = AuthElement {
                    key: ret.bounds[1],
                    digest: [0; DIGEST_SIZE],
                    pointer: new_pointer,
                };

                ret.compute_hash(&mut new_element.digest);
                spare_elements.push(new_element);
                work_set.cache.insert(new_pointer, Mutex::new(ret));
            }
        }

        this_node.split_update(
            returns,
            spare_elements.len() - intitial_spare_elements,
            &mut spare_elements[intitial_spare_elements..].iter().peekable(),
        );
        spare_elements.truncate(intitial_spare_elements);
        work_set.remove.push(pointer);
    }

    pub fn walk(&self) -> Vec<AuthElement> {
        let mut v = Vec::new();
        self._walk(self.root.unwrap(), &mut v);
        v
    }

    fn _walk(&self, pointer: Pointer, result: &mut Vec<AuthElement>) {
        if !self.cache.contains_key(&pointer) {
            println!("Missing key: {}", pointer);
        }

        let node = &self.cache[&pointer].lock();
        if node.leaf {
            for i in 0..node.elements {
                result.push(*node.get_by_position(i));
            }
        } else {
            for i in 0..node.elements {
                let elem = node.get_by_position(i);
                self._walk(elem.pointer, result);
            }
        }
    }
}

#[derive(Clone)]
pub enum AuthOp {
    Insert(AuthElement),
    Delete(AKey),
}

impl AuthOp {
    pub fn key(&self) -> &AKey {
        match self {
            AuthOp::Insert(elem) => &elem.key,
            AuthOp::Delete(key) => key,
        }
    }

    pub fn unwrap_insert(&self) -> &AuthElement {
        if let AuthOp::Insert(elem) = &self {
            return elem;
        }
        panic!("Expected an Insert.")
    }
}

#[derive(Clone, Default, Copy)]
pub struct AuthElement {
    pub key: AKey,
    pub pointer: Pointer,
    pub digest: ADigest,
}

pub enum GetPointer {
    Goto(usize),
    Found(usize),
    NotFound,
}

#[derive(Clone)]
pub struct AuthTreeInternalNode {
    pub updated : bool,
    pub leaf: bool,                 // true if this is a leaf node
    pub elements: usize,            // number of elements in the node
    pub bounds: [AKey; 2],          // the min and max key (inclusive)
    pub items: [AuthElement; NODE_CAPACITY]
}

impl AuthTreeInternalNode {
    pub fn empty(
        leaf: bool,
        bounds: [AKey; 2],
    ) -> AuthTreeInternalNode {
        // Initialize memory
        let new_node = AuthTreeInternalNode {
            updated : false,
            leaf,
            elements: 0,
            bounds,
            items: [Default::default(); NODE_CAPACITY],
        };

        new_node
    }

    pub fn new<'x, T>(
        leaf: bool,
        bounds: [AKey; 2],
        iter: &mut Peekable<T>,
        capacity: usize,
    ) -> AuthTreeInternalNode
    where
        T: Iterator<Item = &'x AuthElement>,
    {

        if capacity > NODE_CAPACITY {
            panic!(
                "Requested capacity must not exceed node capacity: {:?}",
                capacity
            );
        }

        let mut new_node = Self::empty(leaf, bounds);
        loop {
            let peek_element = iter.peek();

            // We have no more items to include so we stop
            if peek_element.is_none() {
                // Since we may be able to add more elements here
                // we extend the bound to what we were given.
                new_node.bounds[1] = bounds[1];
                break;
            }

            // The next element is too large, bail out
            let peek_key = &peek_element.unwrap().key;
            if !(peek_key <= &bounds[1]) {
                // Since we may be able to add more elements here
                // we extend the bound to what we were given.
                new_node.bounds[1] = bounds[1];
                break;
            }

            // The node is full but there are more
            // elements in the stream.
            if new_node.elements == capacity {
                // we keep the right bound as the largest element.
                break;
            }

            // Safe to unwrap due to previous check.
            let new_element = iter.next().unwrap();
            new_node.push_sorted(new_element);
            new_node.bounds[1] = new_element.key;
        }

        // Check tree invariants
        // new_node._check_invariants();
        new_node
    }

    fn _check_invariants(&self) {
        let mut old_key = None;
        for i in 0..self.elements {
            let elem = self.get_by_position(i);
            if !(self.bounds[0] <= elem.key) {
                println!("{:?}", self);
            }
            assert!(self.bounds[0] <= elem.key);
            assert!(elem.key <= self.bounds[1]);
            if let Some(old_val) = old_key {
                if !(old_val < elem.key) {
                    println!("{:?}", self);
                }
                assert!(old_val < elem.key);
            }

            old_key = Some(elem.key);
        }
    }

    pub fn get(&self, key: &AKey) -> GetPointer {
        if self.leaf {
            for i in 0..self.elements {
                let elem = self.get_by_position(i);
                if &elem.key == key {
                    return GetPointer::Found(elem.pointer);
                }
                if &elem.key > key {
                    return GetPointer::NotFound;
                }
            }

            return GetPointer::NotFound;
        } else {
            for i in 0..self.elements {
                let elem = self.get_by_position(i);
                if elem.key >= *key {
                    return GetPointer::Goto(elem.pointer);
                }
            }
            unreachable!();
        }
    }

    pub fn push_sorted(&mut self, new_element: &AuthElement) {
        assert!(self.elements < NODE_CAPACITY);
        self.items[self.elements] = *new_element;
        self.elements += 1;
    }

    pub fn get_by_position(&self, position: usize) -> &AuthElement {
        assert!(position < self.elements);
        &self.items[position]
    }

    pub fn merge_into_leaf<'x, T>(
        &self,
        returns: &mut Vec<Box<Self>>,
        spare_elements: &mut Vec<AuthElement>,
        iter: &mut Peekable<T>,
    ) where
        T: Iterator<Item = &'x AuthOp>,
    {
        // Inefficient, but correct to start with:
        let mut position = 0; // The position we are in this block.
        let initial_spare_elements = spare_elements.len();

        loop {
            let peek_element = iter.peek();

            let self_list_finished: bool = !(position < self.elements);
            let iter_finished: bool =
                peek_element.is_none() || !(peek_element.unwrap().key() <= &self.bounds[1]);

            // If both are finished the break, we are done
            if self_list_finished && iter_finished {
                break;
            }

            // If iterator is finished OR next iterator key is larger than self key
            if !self_list_finished
                && (iter_finished || &self.get_by_position(position).key < peek_element.unwrap().key())
            {
                spare_elements.push(*self.get_by_position(position));
                position += 1;
                continue;
            }

            // If we are here, we are going to need the next iterator element.
            let new_element = iter.next().unwrap();

            if (self_list_finished && !iter_finished)
                || new_element.key() < &self.get_by_position(position).key
            {
                // The iterator element takes priority.
                if let AuthOp::Insert(elem) = new_element{
                    spare_elements.push(*elem);
                }
                // Simply ignore they keys to be deleted if not in DB
                continue;
            }

            if new_element.key() == &self.get_by_position(position).key {
                // The new element takes priority AND we drop the self element (replace)
                if let AuthOp::Insert(elem) = new_element{
                    spare_elements.push(*elem);
                }
                // Skip to delete
                position += 1;
                continue;
            }
        }

        // Now we have a list (spare_elements) with element we need to make one or more
        // AuthTreeInternalNode with.
        let size = spare_elements.len() - initial_spare_elements;
        let xref = &mut spare_elements[initial_spare_elements..].iter().peekable();
        self.split_update(returns, size, xref);
        spare_elements.truncate(initial_spare_elements);
    }

    pub fn split_update<'x, T>(&self, returns: &mut Vec<Box<Self>>, size: usize, xref: &mut Peekable<T>)
    where
        T: Iterator<Item = &'x AuthElement>,
    {
        if size == 0 {
            return
        }

        // Compute the averageoccupancy of a block:
        let mut num_of_blocks = size / NODE_CAPACITY;
        if size % NODE_CAPACITY > 0 {
            num_of_blocks += 1;
        }
        let occupancy = size / num_of_blocks;

        // Initial min is the split block mininmum
        let mut min_key = self.bounds[0];
        loop {
            if xref.peek().is_none() {
                // No elements remainings to be added, so we stop.
                break;
            }

            let next_key = &xref.peek().unwrap().key;
            if !(next_key <= &self.bounds[1]) {
                // We have ran out of elements for this block.
                break;
            }

            // Create the entry
            let entry = AuthTreeInternalNode::new(
                self.leaf,
                [min_key, self.bounds[1]],
                xref,
                occupancy,
            );

            if entry.leaf {
                min_key = entry.bounds[1];
            }

            returns.push(Box::new(entry));
        }
    }

    pub fn is_full(&self) -> bool {
        self.elements == NODE_CAPACITY
    }

    pub fn compute_hash(&mut self, digest_out: &mut [u8; DIGEST_SIZE]) {
        let mut sha3 = Sha3::v224();

        if self.leaf {
            // For leafs we commit to: bounds, keys digests
            sha3.update(&self.elements.to_be_bytes());
            for i in 0..self.elements {
                let elem = self.get_by_position(i);
                sha3.update(&elem.key);
                sha3.update(&elem.digest);
            }
        } else {
            // for internal nodes we commit to digests only
            for i in 0..self.elements {
                let elem = self.get_by_position(i);
                sha3.update(&elem.digest);
            }
        }
        sha3.finalize(digest_out);
    }
}

use std::fmt;

impl fmt::Debug for AuthTreeInternalNode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut fx = if self.leaf {
            f.debug_struct("Leaf")

        } else {
            f.debug_struct("Branch")
        };
        let mut x = Vec::new();
        for i in 0..self.elements {
            let k = self.get_by_position(i);
            let mut v = [0_u8; 8];
            v.clone_from_slice(&k.key[..8]);
            x.push((k.pointer, usize::from_be_bytes(v)));
        }

        let mut min: [u8; 8] = Default::default();
        min.clone_from_slice(&self.bounds[0][0..8]);
        let mut max: [u8; 8] = Default::default();
        max.clone_from_slice(&self.bounds[1][0..8]);

        fx.field("B", &[u64::from_be_bytes(min), u64::from_be_bytes(max)])
            .field("P", &x)
            .finish()
    }
}

#[derive(Debug, Clone)]
pub struct AuthTreeEntry {
    key: AKey,
    digest: [u8; DIGEST_SIZE],
    path: Vec<u8>,
    data: Vec<u8>,
}

impl AuthTreeEntry {
    pub fn get_test_entry(num: u64) -> AuthTreeEntry {
        let mut entry = AuthTreeEntry {
            key: [0; KEY_SIZE],
            digest: [0; DIGEST_SIZE],
            path: vec![1; 56],
            data: vec![2; 300],
        };

        entry.key[..8].clone_from_slice(&num.to_be_bytes());
        entry
    }
}

pub(crate) fn get_test_entry(num: usize) -> AuthElement {
    let mut key = [0; KEY_SIZE];
    let pointer = num;
    let digest = [0; DIGEST_SIZE];
    key[..8].clone_from_slice(&num.to_be_bytes());

    AuthElement {
        key,
        pointer,
        digest,
    }
}
