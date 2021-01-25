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
    for entry in vec1 {
        tree.insert(entry);
    }
    println!("Insert New:  {}ns\ttotal: {}ms", now.elapsed().as_nanos() / EXP as u128, now.elapsed().as_millis());

}

type AKey = [u64; 4];
type ADigest = [u8; 224 / 8];
type Pointer = usize;

const NODE_CAPACITY: usize = 32;
const NULL_DIGEST: ADigest = [0; 224 / 8];

#[derive(Debug)]
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
            cache: HashMap::with_capacity(50000),
            data:  HashMap::with_capacity(50000),
            next_pointer: 0,
        }
    }

    fn update_hashes(&mut self) {
        if let Some(root) = self.root {
            self._update_hashes(&root);
        }
    }

    fn _update_hashes(&mut self, pointer : &Pointer) {
        let target = self.get_pointer(pointer).unwrap();
        if !target.leaf {
            let mut entry_copy = target.clone();
            for idx in 0..entry_copy.elements+1 {
                // Update the child first
                let child_pointer = entry_copy.pointers[idx];
                if self.cache.contains_key(&child_pointer){
                    self._update_hashes(&child_pointer);
                }
                // Then update from the child the copy
                let child = self.get_pointer(&child_pointer).unwrap();

                let mut sha3 = Sha3::v224();
                let offset = if child.leaf { 0 } else { 1 };
                for idx in 0..(child.elements + offset) {
                    // sha3.update(&child.keys[idx]);
                    sha3.update(&child.digests[idx]);
                }
                sha3.finalize(&mut entry_copy.digests[idx]);
            }

            let target = self.cache.get_mut(pointer).unwrap();
            target.digests[..target.elements+1].clone_from_slice(&entry_copy.digests[..entry_copy.elements+1]);
        }

    }



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

                if current_node.keys[idx] == *key {
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

    fn insert_sorted<I>(&mut self, vals: I)
        where
            I: IntoIterator<Item = AuthTreeEntry>,
    {
        let mut iter = vals.into_iter();

        let mut curent_pointer;
        let mut block : &mut AuthTreeInternalNode;
        let mut prev_key;

        if let Some(first_entry) = iter.next() {

            curent_pointer = self.insert(first_entry);
            block = self.cache.get_mut(&curent_pointer).unwrap();
            prev_key = block.keys[0];
        }
        else {
            return
        }

        while let Some(entry) = iter.next() {
            if block.elements < NODE_CAPACITY && prev_key <= entry.key && entry.key < block.keys[block.elements-1] {
                let index = block.get_index(&entry.key);

                if block.keys[index] != entry.key {

                    // Replicate the next pointer functionality here.
                    let entry_pointer = self.next_pointer;
                    self.next_pointer += 1;

                    block.insert_at(index, &entry.key, entry_pointer, &entry.digest);
                    self.data.insert(entry_pointer, entry);
                }
                else{
                    let entry_pointer = block.pointers[index];
                    *self.data.get_mut(&entry_pointer).unwrap() = entry;
                }
            }
            else
            {
                curent_pointer = self.insert(entry);
                block = self.cache.get_mut(&curent_pointer).unwrap();
                prev_key = block.keys[0];
            }
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

    fn next_pointer(&mut self) -> Pointer {
        let current_pointer = self.next_pointer;
        self.next_pointer += 1;
        current_pointer
    }
}

#[derive(Clone)]
struct AuthTreeInternalNode {
    leaf: bool,
    elements: usize,
    keys: [AKey; NODE_CAPACITY],
    pointers: [Pointer; NODE_CAPACITY + 1],
    digests: [ADigest; NODE_CAPACITY + 1],
}

impl AuthTreeInternalNode {

    fn new(
        leaf : bool,
        elements: usize,
        keys: &[AKey],
        pointers: &[Pointer],
        digests: &[ADigest],
    ) -> AuthTreeInternalNode {

        // Check length invariants
        if leaf {
            assert!(keys.len() == elements);
            assert!(keys.len() == pointers.len());
            assert!(digests.len() == pointers.len());
        }
        else {
            assert!(keys.len() == elements);
            assert!(keys.len()+1 == pointers.len());
            assert!(digests.len() == pointers.len());
        }

        // Why Safe: the AuthTreeInternalNode structure contains data arrays,
        // and an initial elements usize. The arrays can be safely zeroed, and
        // the initial elements = 0 is the safe default.
        let mut new_node = unsafe { std::mem::zeroed::<AuthTreeInternalNode>() };

        new_node.leaf = leaf;
        new_node.elements = elements;
        new_node.keys[..keys.len()].clone_from_slice(keys);
        new_node.pointers[..pointers.len()].clone_from_slice(pointers);
        new_node.digests[..digests.len()].clone_from_slice(digests);
        new_node
    }

    fn get_index(&self, key: &AKey) -> usize {
        let idx2 = match &self.keys[0..self.elements].binary_search(key) {
            Ok(pos) => *pos,
            Err(pos) => *pos,
        };

        return idx2;

        /*
        for idx in 0..self.elements {
            if key <= &self.keys[idx] {
                assert!(idx == idx2);
                return idx;
            }
        }
        return self.elements;
        */
    }

    fn insert_at(
        &mut self,
        index: usize,
        key: &AKey,
        new_pointer: Pointer,
        new_digest: &ADigest,
    ) {
        let offset = if self.leaf { 0 } else { 1 };

        // Shift keys to the right
        self.keys.copy_within(index..self.elements, index + 1);
        self.keys[index] = *key;

        // Shift pointers to the right
        self.pointers
            .copy_within(index+offset..self.elements + offset, index + 1+ offset);
            self.pointers[index+offset] = new_pointer;

        // Shift digests to the right
        self.digests
            .copy_within(index+offset..self.elements + offset, index + 1+ offset);
            self.digests[index+offset] = *new_digest;

            self.elements += 1;

        return
    }

    fn is_full(&self) -> bool {
        self.elements == NODE_CAPACITY
    }

    fn _interal_check(&self) {
        let mut prev_k = self.keys[0];
        for k in 1..self.elements {
            assert!(prev_k <= self.keys[k]);
            prev_k = self.keys[k];
        }
    }

}

use std::fmt;

impl fmt::Debug for AuthTreeInternalNode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.leaf {
            f.debug_struct("Leaf")
            .field("L", &self.elements)
            .field("K", &self.keys[..self.elements].to_vec())
            .field("P", &self.pointers[..self.elements].to_vec())
            .finish()
        } else {
            f.debug_struct("Branch")
            .field("L", &self.elements)
            .field("K", &self.keys[..self.elements].to_vec())
            .field("P", &self.pointers[..self.elements+1].to_vec())
            .finish()
        }
    }
}


#[derive(Debug, Clone)]
struct AuthTreeEntry {
    key: AKey,
    digest: [u8; 224 / 8],
    path: Vec<u8>,
    data: Vec<u8>,
}

impl AuthTreeEntry {
    fn get_test_entry(num : u64) -> AuthTreeEntry {
        let mut entry = AuthTreeEntry {
            key : [num; 4],
            digest: [0; 224/8],
            path: vec![1; 56],
            data: vec![2; 300],
        };

        entry._compute_hash();
        entry
    }

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
}


/*

sha3.update(b"hello");
    let mut sha3 = Sha3::224();
    sha3.update(b" ");
    sha3.update(b"world");
    sha3.finalize(&mut output);

*/


#[cfg(test)]
mod tests {
    use super::*;
    use std::time::{Instant, };
    use rand::thread_rng;
    use rand::seq::SliceRandom;

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
}
