use std::collections::HashMap;
use std::slice;
use tiny_keccak::{Hasher, Sha3};

fn main() {
    use rand::seq::SliceRandom;
    use rand::thread_rng;
    use std::time::Instant;

    const EXP: u64 = 200_000;
    let mut tree = TreeCache::new();
    let mut vec: Vec<AuthTreeEntry> = (0..EXP)
        .map(|num| AuthTreeEntry::get_test_entry(2 * num))
        .collect();
    vec.shuffle(&mut thread_rng());

    let vec1 = vec.clone();
    let now = Instant::now();
    /*
    for entry in vec1 {
        tree.insert(entry);
    }
    */
    println!(
        "Insert New:  {}ns\ttotal: {}ms",
        now.elapsed().as_nanos() / EXP as u128,
        now.elapsed().as_millis()
    );
}

const NODE_CAPACITY: usize = 30;
const KEY_SIZE: usize = 20;
const DIGEST_SIZE: usize = 224 / 8;
const NULL_DIGEST: ADigest = [0; DIGEST_SIZE];

type AKey = [u8; KEY_SIZE];
type ADigest = [u8; DIGEST_SIZE];
type Pointer = usize;

const MIN_KEY: AKey = [0; KEY_SIZE];
const MAX_KEY: AKey = [255; KEY_SIZE];

// #[derive(Debug)]
struct TreeCache {
    root: Option<usize>,
    cache: HashMap<usize, AuthTreeInternalNode>,
    data: HashMap<usize, AuthTreeEntry>,
    next_pointer: usize,
}

impl TreeCache {
    fn new() -> TreeCache {
        TreeCache {
            root: None,
            cache: HashMap::with_capacity(500),
            data: HashMap::with_capacity(500),
            next_pointer: usize::MAX / 2,
        }
    }

    fn next_pointer(&mut self) -> Pointer {
        let current_pointer = self.next_pointer;
        self.next_pointer += 1;
        current_pointer
    }

    fn update_with_elements<T>(&mut self, iter: &mut Peekable<T>) where
        T: IntoIterator<Item = AuthElement> + Iterator<Item = AuthElement>,
    {
        // First deal with the case there is no root. Then we just make an empty one.
        let root_pointer = if self.root.is_none(){
            let root = AuthTreeInternalNode::empty(true, [MIN_KEY, MAX_KEY], None);
            let root_pointer =  self.next_pointer();
            self.cache.insert(root_pointer, root);
            self.root = Some(root_pointer);
            root_pointer
        }
        else {
            self.root.unwrap()
        };

        // Make some temporary structures.
        let mut returns = Vec::with_capacity(NODE_CAPACITY);
        let mut spare_elements = Vec::with_capacity(NODE_CAPACITY);

        self.update(&mut returns, &mut spare_elements, root_pointer, iter);

        loop {
            // Now we reduce the number of returns by constructing the tree

            let number_of_returns = returns.len();

            // Save the new nodes in the cache, and add them to the list.
            for ret in returns.drain(..) {
                let new_pointer = self.next_pointer();
                let new_element = AuthElement {
                    key: ret.bounds[1],
                    digest: [0; DIGEST_SIZE], // FIX (security): compute the hash here.
                    pointer: new_pointer,
                };
                spare_elements.push(new_element);
                self.cache.insert(new_pointer, ret);

                if number_of_returns == 1 {
                    // This is the new root, save and exit.
                    self.root = Some(new_pointer);
                    // Remove the old root
                    self.cache.remove(&root_pointer);
                    return
                }
            }

            let root_node = &self.cache[&root_pointer];
            root_node.split_update(
                &mut returns,
                spare_elements.len(),
                &mut spare_elements.drain(..).peekable(),
            );

        }


    }

    fn update<T>(
        &mut self,
        returns: &mut Vec<AuthTreeInternalNode>,
        spare_elements: &mut Vec<AuthElement>,
        pointer: Pointer,
        iter: &mut Peekable<T>,
    ) where
        T: IntoIterator<Item = AuthElement> + Iterator<Item = AuthElement>,
    {
        let mut this_node = &self.cache[&pointer];
        let intitial_returns = returns.len();
        let intitial_spare_elements = spare_elements.len();

        if this_node.leaf {
            this_node.merge(returns, spare_elements, iter);
            return;
        }

        // This is an internal node
        let this_node_len = this_node.elements;
        for i in 0..this_node_len - 1 {
            let peek_next = iter.peek();

            let this_child_ref = this_node.get_by_position(i);
            if peek_next.is_none() || !(peek_next.unwrap().key < this_child_ref.key) {
                // We do not need to explore in this child, so we simply add the element to the spares list
                spare_elements.push(*this_child_ref) // FIX (perf): COPY HERE
            } else {
                // We need to explore down this child
                let child_pointer = this_child_ref.pointer;
                drop(this_node);
                self.update(returns, spare_elements, child_pointer, iter);

                // Save the new nodes in the cache, and add them to the list.
                for ret in returns.drain(intitial_returns..) {
                    let new_pointer = self.next_pointer();
                    let new_element = AuthElement {
                        key: ret.bounds[1],
                        digest: [0; DIGEST_SIZE], // FIX (security): compute the hash here.
                        pointer: new_pointer,
                    };
                    spare_elements.push(new_element);
                    self.cache.insert(new_pointer, ret);
                }

                // Now get back the node we were considering
                this_node = &self.cache[&pointer]; // FIX (perf): LOOKUP HERE
            }
        }

        this_node.split_update(
            returns,
            spare_elements.len() - intitial_spare_elements,
            &mut spare_elements.drain(intitial_spare_elements..).peekable(),
        );

        self.cache.remove(&pointer);
    }

}

#[derive(Clone, Default, Copy)]
struct AuthElement {
    key: AKey,
    pointer: Pointer,
    digest: ADigest,
}

#[derive(Clone)]
struct AuthTreeInternalNode {
    leaf: bool,                 // true if this is a leaf node
    elements: usize,            // number of elements in the node
    bounds: [AKey; 2],          // the min and max key (inclusive)
    slots: [u8; NODE_CAPACITY], // Ordered indexes of elements in node
    items: [AuthElement; NODE_CAPACITY],
    left_pointer: Option<(Pointer, ADigest)>,
}

use std::collections::VecDeque;
use std::iter::Iterator;
use std::iter::Peekable;

impl AuthTreeInternalNode {
    fn empty(
        leaf: bool,
        mut bounds: [AKey; 2],
        left_pointer: Option<(Pointer, ADigest)>,
    ) -> AuthTreeInternalNode {
        // Initialize memory
        let mut slots = [0; NODE_CAPACITY];
        for i in 0..NODE_CAPACITY {
            slots[i] = i as u8;
        }

        let new_node = AuthTreeInternalNode {
            leaf,
            elements: 0,
            bounds,
            slots: slots,
            items: [Default::default(); NODE_CAPACITY],
            left_pointer,
        };

        new_node
    }

    fn new<T>(
        leaf: bool,
        mut bounds: [AKey; 2],
        left_pointer: Option<(Pointer, ADigest)>,
        iter: &mut Peekable<T>,
        capacity: usize,
    ) -> AuthTreeInternalNode
    where
        T: IntoIterator<Item = AuthElement> + Iterator<Item = AuthElement>,
    {
        if !leaf && left_pointer.is_some() {
            panic!("Leaf cannot have left pointer");
        };

        if capacity > NODE_CAPACITY {
            panic!(
                "Requested capacity must not exceed node capacity: {:?}",
                capacity
            );
        }

        let mut new_node = Self::empty(leaf, bounds, left_pointer);
        loop {
            let peek_element = iter.peek();

            // We have no more items to include so we stop
            if peek_element.is_none() {
                break;
            }

            // The next element is too large, bail out
            let peek_key = peek_element.unwrap().key;
            if !(peek_key < bounds[1] || peek_key == MAX_KEY) {
                break;
            }

            // Safe to unwrap due to previous check.
            let new_element = iter.next().unwrap();
            new_node.push_sorted(&new_element);

            // The node is full we now must stop
            if new_node.elements == capacity {
                new_node.bounds[1] = new_node.items[new_node.elements - 1].key; // Set the last key as max right bound
                break;
            }
        }

        new_node
    }

    fn push_sorted(&mut self, new_element: &AuthElement) {
        self.elements += 1;
        let position = self.slots[self.elements - 1];
        self.items[position as usize] = *new_element;
    }

    fn get_by_position(&self, position: usize) -> &AuthElement {
        assert!(position < self.elements);
        let inner_position = self.slots[position];
        &self.items[inner_position as usize]
    }

    fn merge<T>(
        &self,
        returns: &mut Vec<Self>,
        spare_elements: &mut Vec<AuthElement>,
        iter: &mut Peekable<T>,
    ) where
        T: IntoIterator<Item = AuthElement> + Iterator<Item = AuthElement>,
    {
        // Inefficient, but correct to start with:
        let mut position = 0; // The position we are in this block.
        let initial_spare_elements = spare_elements.len();
        let initial_returns = returns.len();

        loop {
            let peek_element = iter.peek();
            if peek_element.is_some() {
                if !(peek_element.unwrap().key < self.bounds[1]) {
                    // We ran out of elements within the appropriate bounds.
                    break;
                }
            }

            let self_list_finished: bool = !(position < self.elements);
            let iter_finished: bool = peek_element.is_none();

            // If both are finished the break, we are done
            if self_list_finished && iter_finished {
                break;
            }

            // If iterator is finished OR next iterator key is larger than self key
            if !self_list_finished
                && (iter_finished || self.get_by_position(position).key < peek_element.unwrap().key)
            {
                spare_elements.push(*self.get_by_position(position));
                position += 1;
                continue;
            }

            // If we are here, we are going to need the next iterator element.
            drop(peek_element);
            let new_element = iter.next().unwrap();

            if (self_list_finished && !iter_finished)
                || new_element.key < self.get_by_position(position).key
            {
                // The iterator element takes priority.
                spare_elements.push(new_element);
                continue;
            }

            if new_element.key == self.get_by_position(position).key {
                // The new element takes priority AND we drop the self element (replace)
                spare_elements.push(new_element);
                position += 1;
                continue;
            }
        }

        // Now we have a list (spare_elements) with element we need to make one or more
        // AuthTreeInternalNode with.
        let size = spare_elements.len() - initial_spare_elements;
        let xref = &mut spare_elements.drain(initial_spare_elements..).peekable();
        self.split_update(returns, size, xref);
    }

    fn split_update<T>(&self, returns: &mut Vec<Self>, size: usize, xref: &mut Peekable<T>)
    where
        T: IntoIterator<Item = AuthElement> + Iterator<Item = AuthElement>,
    {
        // Compute the averageoccupancy of a block:
        let mut num_of_blocks = size / (NODE_CAPACITY - 1);
        if size % (NODE_CAPACITY - 1) > 0 {
            num_of_blocks += 1;
        }
        let occupancy = size / num_of_blocks;

        // Track how many we have added
        let mut number_added = 0;
        // Initial min is the split block mininmum
        let mut min_key = self.bounds[0];
        loop {
            if xref.peek().is_none() {
                // No elements reamining to be added, so we stop.
                break;
            }

            if number_added > 0 {
                // Min key is the first element (except for first block)
                min_key = xref.peek().unwrap().key;
            }

            if !(min_key < self.bounds[1] || min_key == MAX_KEY) {
                // We have ran out of elements for this block.
                break
            }

            // Create the entry
            let mut entry = AuthTreeInternalNode::new(
                self.leaf,
                [min_key, self.bounds[1]],
                None,
                xref,
                occupancy,
            );

            // Update the past block added max-key according to the
            // min bound of this block.
            if number_added > 0 {
                returns.last_mut().unwrap().bounds[1] = entry.bounds[0];
            }

            entry.bounds[1] = self.bounds[1];
            returns.push(entry);
            number_added += 1;
        }

    }

    fn is_full(&self) -> bool {
        self.elements == NODE_CAPACITY
    }
}

use std::fmt;

impl fmt::Debug for AuthTreeInternalNode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut fx = if self.leaf {
            f.debug_struct("Leaf")
        // .field("V", &self.bounds)
        // .finish()
        } else {
            f.debug_struct("Branch")
            // .field("V", &self.elements)
            // .finish()
        };
        let mut x = Vec::new();
        for i in 0..self.elements {
            let k = self.get_by_position(i);
            x.push(k.pointer);
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
struct AuthTreeEntry {
    key: AKey,
    digest: [u8; DIGEST_SIZE],
    path: Vec<u8>,
    data: Vec<u8>,
}

impl AuthTreeEntry {
    fn get_test_entry(num: u64) -> AuthTreeEntry {
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

#[cfg(test)]
mod tests {
    use super::*;
    use rand::seq::SliceRandom;
    use rand::thread_rng;
    use std::time::Instant;

    fn get_test_entry(num: usize) -> AuthElement {
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

    #[test]
    fn endianness_to_ord() {
        for x in 500..600 {
            let x100 = get_test_entry(x);
            let x200 = get_test_entry(x + 1);
            assert!(x100.key < x200.key);
        }
    }

    #[test]
    fn construct_leaf() {
        let x: Vec<AuthElement> = (0..100).map(|num| get_test_entry(num)).collect();
        let entry = AuthTreeInternalNode::new(
            true,
            [MIN_KEY, MAX_KEY],
            None,
            &mut x.into_iter().peekable(),
            10,
        );

        assert!(entry.elements == 10);
        assert!(entry.bounds[1] == get_test_entry(9).key);
    }

    #[test]
    fn construct_leaf_with_max() {
        let x: Vec<AuthElement> = (0..100).map(|num| get_test_entry(num)).collect();
        let entry = AuthTreeInternalNode::new(
            true,
            [MIN_KEY, get_test_entry(5).key],
            None,
            &mut x.into_iter().peekable(),
            10,
        );

        assert!(entry.elements == 5);
        assert!(entry.bounds[1] == get_test_entry(5).key);
    }

    #[test]
    fn construct_two_leaf_with_max() {
        let x: Vec<AuthElement> = (0..100).map(|num| get_test_entry(num)).collect();
        let x2 = &mut x.into_iter();
        let entry = AuthTreeInternalNode::new(
            true,
            [MIN_KEY, get_test_entry(5).key],
            None,
            &mut x2.into_iter().peekable(),
            10,
        );

        let entry = AuthTreeInternalNode::new(
            true,
            [MIN_KEY, get_test_entry(15).key],
            None,
            &mut x2.into_iter().peekable(),
            10,
        );

        assert!(entry.elements == 9);
        assert!(entry.bounds[1] == get_test_entry(15).key);
    }

    #[test]
    fn construct_leaf_with_merge() {
        let x: Vec<AuthElement> = (0..100).map(|num| get_test_entry(num)).collect();
        let mut iter = x.into_iter().peekable();
        let mut entry = AuthTreeInternalNode::new(true, [MIN_KEY, MAX_KEY], None, &mut iter, 10);

        entry.bounds = [MIN_KEY, MAX_KEY];

        let mut returns = Vec::new();
        let mut spares = Vec::new();
        // println!("START {:?}", entry);
        entry.merge(&mut returns, &mut spares, &mut iter);

        //println!("RET({}) {:?}", returns.len(), returns);
        assert!(returns.len() == 1 + 100 / (NODE_CAPACITY));
    }

    #[test]
    fn construct_leaf_with_merge_empty_start() {
        let x: Vec<AuthElement> = (0..100).map(|num| get_test_entry(num)).collect();
        let mut iter = x.into_iter().peekable();

        let mut entry = AuthTreeInternalNode::empty(true, [MIN_KEY, MAX_KEY], None);

        entry.bounds = [MIN_KEY, MAX_KEY];

        let mut returns = Vec::new();
        let mut spares = Vec::new();
        // println!("START {:?}", entry);
        entry.merge(&mut returns, &mut spares, &mut iter);

        // println!("RET({}) {:?}", returns.len(), returns);
        assert!(returns.len() == 1 + 100 / (NODE_CAPACITY));
    }

    #[test]
    fn construct_tree() {
        const EXP : usize = 100_000;
        let x: Vec<AuthElement> = (0..EXP).map(|num| get_test_entry(num)).collect();
        let mut iter = x.into_iter().peekable();

        let now = Instant::now();
        let mut tree = TreeCache::new();
        tree.update_with_elements(&mut iter);
        let dur = now.elapsed();
        println!("Make Tree: {}ns\ttotal: {}ms", dur.as_nanos() / EXP as u128, dur.as_millis());


        // println!("TREE({}) {:?}", tree.cache.len(), tree.cache);
        // assert!(returns.len() == 1 + 100 / (NODE_CAPACITY));
    }

    /*
    #[test]
    fn insert_contains_not_contains() {

        const EXP : u64 = 100_000;
        let mut tree = TreeCache::new();

        let now = Instant::now();
        let mut vec: Vec<AuthTreeEntry> = (0..EXP).map(|num| AuthTreeEntry::get_test_entry(2*num)).collect();
        println!("Hash Alloc: {}ns\ttotal: {}ms", now.elapsed().as_nanos() / EXP as u128, now.elapsed().as_millis());

        let vec_sorted = vec.clone();
        vec.shuffle(&mut thread_rng());

        let vec1 = vec.clone();
        let now = Instant::now();
        for entry in vec1 {
            tree.insert(entry);
        }
        println!("Insert New:  {}ns\ttotal: {}ms", now.elapsed().as_nanos() / EXP as u128, now.elapsed().as_millis());

        vec.shuffle(&mut thread_rng());
        // println!("Nuber of blocks: {}", tree.cache.len());
        let vec2 = vec.clone();
        let now = Instant::now();
        for entry in vec2 {
            tree.insert(entry);
        }
        println!("Update Old: {}ns\ttotal: {}ms", now.elapsed().as_nanos() / EXP as u128, now.elapsed().as_millis());

        let now = Instant::now();
        tree.insert_sorted(vec_sorted);
        println!("Update Sort: {}ns\ttotal: {}ms", now.elapsed().as_nanos() / EXP as u128, now.elapsed().as_millis());

        let now = Instant::now();
        // println!("Nuber of blocks: {}", tree.cache.len());
        for num in 0..EXP {
            let res = tree.get(&[2*num; 4]);
            assert!(res.unwrap().key[0] == 2*num);
        }
        println!("Get Some:   {}ns\ttotal: {}ms", now.elapsed().as_nanos() / EXP as u128, now.elapsed().as_millis());

        let now = Instant::now();
        //println!("Nuber of blocks: {}", tree.cache.len());
        for num in 0..EXP {
            let res = tree.get(&[2*num + 1; 4]);
            assert!(res.is_none());
        }
        println!("Get None:   {}ns\ttotal: {}ms", now.elapsed().as_nanos() / EXP as u128, now.elapsed().as_millis());

        let now = Instant::now();
        println!("Nuber of blocks: {}", tree.cache.len());
        const NUM : usize = 10;
        for num in 0..NUM {
            tree.update_hashes();
        }
        println!("Update hashes: {}ms\ttotal: {}ms", now.elapsed().as_millis() / NUM as u128, now.elapsed().as_millis());

    }
    */
}

/*
fn _compute_hash(&mut self) {

    // TODO: proper format
    let mut sha3 = Sha3::v224();
    sha3.update(
        unsafe { std::mem::transmute::<&[u64;4],&[u8;4*8]>(&self.key) }
        );
    let path_len = self.path.len().to_be_bytes();
    sha3.update(&path_len[..]);
    sha3.update(&self.path[..]);
    let data_len = self.data.len().to_be_bytes();
    sha3.update(&data_len[..]);
    sha3.update(&self.data[..]);
    sha3.finalize(&mut self.digest[..]);
}
*/
