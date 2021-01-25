use std::collections::HashMap;
use tiny_keccak::{Hasher, Sha3};
use std::slice;

fn main() {

    use std::time::{Instant, };
    use rand::thread_rng;
    use rand::seq::SliceRandom;

    const EXP : u64 = 200_000;
    let mut tree = TreeCache::new();
    let mut vec: Vec<AuthTreeEntry> = (0..EXP).map(|num| AuthTreeEntry::get_test_entry(2*num)).collect();
    vec.shuffle(&mut thread_rng());

    let vec1 = vec.clone();
    let now = Instant::now();
    /*
    for entry in vec1 {
        tree.insert(entry);
    }
    */
    println!("Insert New:  {}ns\ttotal: {}ms", now.elapsed().as_nanos() / EXP as u128, now.elapsed().as_millis());

}

const NODE_CAPACITY: usize = 30;
const KEY_SIZE : usize = 20;
const DIGEST_SIZE : usize = 224 / 8;
const NULL_DIGEST: ADigest = [0; DIGEST_SIZE];

type AKey = [u8; KEY_SIZE];
type ADigest = [u8; DIGEST_SIZE];
type Pointer = usize;

const MIN_KEY : AKey = [0; KEY_SIZE];
const MAX_KEY : AKey = [255; KEY_SIZE];

// #[derive(Debug)]
struct TreeCache {
    root: Option<usize>,
    cache: HashMap<usize, AuthTreeInternalNode>,
    data : HashMap<usize, AuthTreeEntry>,
    next_pointer: usize,
}

impl TreeCache {
    fn new() -> TreeCache {
        TreeCache {
            root: None,
            cache: HashMap::with_capacity(5000),
            data:  HashMap::with_capacity(5000),
            next_pointer: 0,
        }
    }

    /*

    fn get_pointer(&self, pointer: &Pointer) -> Option<&AuthTreeInternalNode> {
        self.cache.get(pointer)
    }

    fn get(&self, key: &AKey) -> Option<&AuthTreeEntry> {
        if self.root.is_none(){
            return None;
        }

        let mut current_pointer = self.root.unwrap();
        let mut current_node = self.get_pointer(&current_pointer).unwrap();
        loop {
            let idx = current_node.get_index(key);
            if current_node.leaf {
                if idx == NODE_CAPACITY {
                    return None;
                }

                if &current_node.keys[idx] == key {
                    let data = self.data.get(&current_node.pointers[idx]).unwrap();
                    return Some(data);
                }
                else {
                    return None
                }
            }

            // Not an index continue the search down the tree
            current_pointer = current_node.pointers[idx];
            current_node = self.get_pointer(&current_pointer).unwrap();
        }
    }

    // Returns the pointer to the Leaf Branch in which we inserted the value
    fn insert(&mut self, entry : AuthTreeEntry) -> Pointer {

        if self.root.is_none(){
            // Empty tree create initial strucutre.

            // First insert the entry
            let entry_pointer = self.next_pointer();

            // Then insert the leaf btree node
            let root_pointer = self.next_pointer();
            let root = AuthTreeInternalNode::new( true, 1, &[ entry.key ], &[ entry_pointer ], &[ entry.digest ] );

            self.data.insert(entry_pointer, entry);
            self.cache.insert(root_pointer, root);

            self.root = Some(root_pointer);
            return root_pointer;
        }

        let mut current_pointer = self.root.unwrap();
        let mut current_node = self.get_pointer(&current_pointer).unwrap();

        // Invariant -- the current node has room for one more entry
        if current_node.is_full(){
            let (key, l, r) = self.split_node(&current_pointer);
            let root = AuthTreeInternalNode::new( false, 1, &[ key ], &[ l, r ], &[ NULL_DIGEST, NULL_DIGEST ] );
            let new_root_pointer = self.next_pointer();
            self.cache.insert(new_root_pointer, root);
            self.root = Some(new_root_pointer);
            current_pointer = new_root_pointer;
            current_node = self.get_pointer(&current_pointer).unwrap();
        }

        loop {
            assert!(self.cache.contains_key(&current_pointer));
            let index = current_node.get_index(&entry.key);

            // Create new entry
            if current_node.leaf && current_node.keys[index] != entry.key {
                let entry_pointer = self.next_pointer();
                self.insert_at(&current_pointer, index, &entry.key, entry_pointer, &entry.digest);
                self.data.insert(entry_pointer, entry);
                return current_pointer;
            }

            // Mutate existing entry
            if current_node.leaf && current_node.keys[index] == entry.key {
                let entry_pointer = current_node.pointers[index];
                *self.data.get_mut(&entry_pointer).unwrap() = entry;
                return current_pointer;
            }

            // This is not a leaf, it is a branch, ensure it is not empty
            let mut child_node_pointer = current_node.pointers[index];
            let mut child_node = self.get_pointer(&child_node_pointer).unwrap();
            if child_node.is_full() {
                drop(current_node);
                drop(child_node);
                {
                    let (key, _, r) = self.split_node(&child_node_pointer);
                    self.insert_at(&current_pointer, index, &key, r, &NULL_DIGEST);
                }

                current_node = self.get_pointer(&current_pointer).unwrap();
                let index = current_node.get_index(&entry.key);
                child_node_pointer = current_node.pointers[index];
                child_node = self.get_pointer(&child_node_pointer).unwrap();
            }

            current_pointer = child_node_pointer;
            current_node = child_node;
        }

    }

    fn insert_at(
        &mut self,
        pointer: &Pointer,
        index: usize,
        key: &AKey,
        new_pointer: Pointer,
        new_digest: &ADigest,
    ) {
        let node = self.cache.get_mut(pointer).unwrap();
        node.insert_at(index, key, new_pointer, new_digest);
    }

    fn split_node(
        &mut self,
        child_pointer: &Pointer,
    ) -> (AKey, Pointer, Pointer) {
        let new_pointer_right = self.next_pointer();
        let right_elem;
        let pivot;

        // Mutate the left hand side, and create the new right hand side
        if let Some(node) = self.cache.get_mut(child_pointer) {
            assert!(node.elements == NODE_CAPACITY);

            let pivot_index = NODE_CAPACITY / 2;
            pivot = node.keys[pivot_index];

            if node.leaf {
                // We need to copy over all entries -- for a leaf
                let right_len = NODE_CAPACITY - pivot_index;
                right_elem = AuthTreeInternalNode::new(
                    true,
                    right_len-1,
                    &node.keys[pivot_index+1..node.elements],
                    &node.pointers[pivot_index+1..node.elements],
                    &node.digests[pivot_index+1..node.elements],
                );

            node.elements = pivot_index+1;
            }
            else {
                // We copy the pointers
                let right_len = NODE_CAPACITY - pivot_index;
                right_elem = AuthTreeInternalNode::new(
                    false,
                    right_len-1, // We do not copy over the pivot.
                    &node.keys[pivot_index+1..node.elements],
                    &node.pointers[pivot_index+1..node.elements+1],
                    &node.digests[pivot_index+1..node.elements+1],
                );
                node.elements = pivot_index;
            }

            #[cfg(debug_assertions)]
            {
                node._interal_check();
                right_elem._interal_check();
                assert!(node.keys[node.elements-1] <= pivot);
                assert!(right_elem.keys[right_elem.elements-1] > pivot);
            }


        } else {
            panic!("Pointer must exist in the table.")
        }

        self.cache
            .insert(new_pointer_right, right_elem);

        return (pivot, *child_pointer, new_pointer_right);
    }

    */

    fn next_pointer(&mut self) -> Pointer {
        let current_pointer = self.next_pointer;
        self.next_pointer += 1;
        current_pointer
    }
}

#[derive(Clone, Default, Copy)]
struct AuthElement {
    key : AKey,
    pointer : Pointer,
    digest: ADigest,
}

#[derive(Clone)]
struct AuthTreeInternalNode {
    leaf: bool,                 // true if this is a leaf node
    elements: usize,            // number of elements in the node
    bounds: [AKey; 2],          // the min and max key (inclusive)
    slots: [u8 ; NODE_CAPACITY],    // Ordered indexes of elements in node
    items : [ AuthElement ; NODE_CAPACITY ],
    left_pointer : Option<(Pointer, ADigest)>,
}

use std::iter::Peekable;
use std::iter::Iterator;
use std::collections::VecDeque;

impl AuthTreeInternalNode {

    fn new<T>(
        leaf : bool,
        mut bounds: [AKey; 2],
        left_pointer : Option<(Pointer, ADigest)>,
        iter : &mut  Peekable<T>,
        capacity : usize,
    ) -> AuthTreeInternalNode
    where
        T: IntoIterator<Item = AuthElement> + Iterator<Item = AuthElement>,
    {
        if !leaf && left_pointer.is_some() {
            panic!("Leaf cannot have left pointer");
        };

        if capacity > NODE_CAPACITY {
            panic!("Requested capacity must not exceed node capacity: {:?}", capacity);
        }

        // Initialize memory
        let mut slots = [0; NODE_CAPACITY];
        for i in 0..NODE_CAPACITY {
            slots[i] = i as u8;
        }

        let mut new_node = AuthTreeInternalNode {
            leaf,
            elements : 0,
            bounds,
            slots : slots,
            items : [ Default::default(); NODE_CAPACITY ],
            left_pointer,
        };


        loop {
            let peek_element = iter.peek();

            // We have no more items to include so we stop
            if peek_element.is_none() {
                break
            }

            // The next element is too large, bail out
            let peek_key = peek_element.unwrap().key;
            if !(peek_key < bounds[1]) {                break
            }

            // Safe to unwrap due to previous check.
            let new_element = iter.next().unwrap();
            new_node.push_sorted(&new_element);

            // The node is full we now must stop
            if new_node.elements == capacity {
                new_node.bounds[1] = new_node.items[new_node.elements - 1].key; // Set the last key as max right bound
                break
            }
        }

        new_node
    }

    fn push_sorted(&mut self, new_element : &AuthElement) {
        self.elements += 1;
        let position = self.slots[self.elements - 1];
        self.items[position as usize] = *new_element;
    }

    fn get_by_position(&self, position: usize) -> &AuthElement {
        assert!(position < self.elements);
        let inner_position = self.slots[position];
        &self.items[inner_position as usize]
    }

    fn merge<T>(&self, returns :  &mut Vec<Self>, spare_elements: &mut Vec<AuthElement>, iter : &mut Peekable<T>) where
        T: IntoIterator<Item = AuthElement> + Iterator<Item = AuthElement>,
    {
        // Inefficient, but correct to start with:
        let mut position = 0; // The position we are in this block.
        loop {
            let peek_element = iter.peek();
            if peek_element.is_some() {
                if !(peek_element.unwrap().key < self.bounds [1]) {
                    panic!("Elements provided must be within bounds.");
                }
            }

            let self_list_finished : bool = !( position < self.elements);
            let iter_finished : bool = peek_element.is_none();

            // If both are finished the break, we are done
            if self_list_finished && iter_finished {
                break
            }

            // If iterator is finished OR next iterator key is larger than self key
            if !self_list_finished && (iter_finished || self.get_by_position(position).key < peek_element.unwrap().key )
            {
                spare_elements.push(*self.get_by_position(position));
                position += 1;
                continue
            }

            // If we are here, we are going to need the next iterator element.
            drop(peek_element);
            let new_element = iter.next().unwrap();

            if (self_list_finished && !iter_finished)
                || new_element.key < self.get_by_position(position).key {
                    // The iterator element takes priority.
                spare_elements.push(new_element);
                continue
            }

            if new_element.key == self.get_by_position(position).key {
                // The new element takes priority AND we drop the self element (replace)
                spare_elements.push(new_element);
                position += 1;
                continue
            }
        }

        // Now we have a list (spare_elements) with element we need to make one or more
        // AuthTreeInternalNode with.

        let mut num_of_blocks = spare_elements.len() / (NODE_CAPACITY - 1);
        if spare_elements.len() % (NODE_CAPACITY - 1) > 0 {
            num_of_blocks += 1;
        }

        let occupancy = spare_elements.len() / num_of_blocks;
        // let mut new_iter = spare_elements.into_iter();
        let xref = &mut spare_elements.drain(..).peekable();

        loop {

            if xref.peek().is_none() {
                break
            }
            let min_key = xref.peek().unwrap().key;

            let entry = AuthTreeInternalNode::new(
                self.leaf ,
                [ min_key, self.bounds[1] ],
                None,
                xref,
                occupancy
            );

            returns.push(entry);
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
            // .field("V", &self.elements)
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
        fx.field("P", &x);
        fx.finish()
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
    fn get_test_entry(num : u64) -> AuthTreeEntry {
        let mut entry = AuthTreeEntry {
            key : [0; KEY_SIZE],
            digest: [0; DIGEST_SIZE],
            path: vec![1; 56],
            data: vec![2; 300],
        };

        entry.key[..8].clone_from_slice(&num.to_be_bytes());
        // entry._compute_hash();
        entry
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
}


#[cfg(test)]
mod tests {
    use super::*;
    use std::time::{Instant, };
    use rand::thread_rng;
    use rand::seq::SliceRandom;


    fn get_test_entry(num : usize) -> AuthElement {
        let mut key = [0; KEY_SIZE];
        let pointer = num;
        let digest = [0; DIGEST_SIZE];
        key[..8].clone_from_slice(&num.to_be_bytes());

        AuthElement {
            key,
            pointer,
            digest
        }
    }

    #[test]
    fn endianness_to_ord() {
        for x in 500..600 {
            let x100 = get_test_entry(x);
            let x200 = get_test_entry(x+1);
            assert!(x100.key < x200.key);
        }
    }

    #[test]
    fn construct_leaf() {
        let x : Vec<AuthElement> = (0..100).map(|num| get_test_entry(num) ).collect();
        let entry = AuthTreeInternalNode::new(
            true,
            [ MIN_KEY, MAX_KEY ],
            None,
            &mut x.into_iter().peekable(),
            10
        );

        assert!(entry.elements == 10);
        assert!(entry.bounds[1] == get_test_entry(9).key);
    }

    #[test]
    fn construct_leaf_with_max() {
        let x : Vec<AuthElement> = (0..100).map(|num| get_test_entry(num) ).collect();
        let entry = AuthTreeInternalNode::new(
            true,
            [ MIN_KEY, get_test_entry(5).key ],
            None,
            &mut x.into_iter().peekable(),
            10
        );

        assert!(entry.elements == 5);
        assert!(entry.bounds[1] == get_test_entry(5).key);
    }

    #[test]
    fn construct_two_leaf_with_max() {
        let x : Vec<AuthElement> = (0..100).map(|num| get_test_entry(num) ).collect();
        let x2 = &mut x.into_iter();
        let entry = AuthTreeInternalNode::new(
            true,
            [ MIN_KEY, get_test_entry(5).key ],
            None,
            &mut x2.into_iter().peekable(),
            10
        );

        let entry = AuthTreeInternalNode::new(
            true,
            [ MIN_KEY, get_test_entry(15).key ],
            None,
            &mut x2.into_iter().peekable(),
            10
        );

        assert!(entry.elements == 9);
        assert!(entry.bounds[1] == get_test_entry(15).key);
    }

    #[test]
    fn construct_leaf_with_merge() {
        let x : Vec<AuthElement> = (0..100).map(|num| get_test_entry(num) ).collect();
        let mut iter = x.into_iter().peekable();
        let mut entry = AuthTreeInternalNode::new(
            true,
            [ MIN_KEY, MAX_KEY ],
            None,
            &mut iter,
            10
        );

        entry.bounds = [ MIN_KEY, MAX_KEY ];

        let mut returns = Vec::new();
        let mut spares  = Vec::new();
        // println!("START {:?}", entry);
        entry.merge(&mut returns, &mut spares, &mut iter);

        // println!("RET({}) {:?}", returns.len(), returns);
        assert!(returns.len() == 1 + 100 / (NODE_CAPACITY));


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
