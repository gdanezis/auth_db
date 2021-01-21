use std::collections::HashMap;
use tiny_keccak::{Hasher, Sha3};


fn main() {
    println!("Hello, world!");
    println!(
        "Block Size: {}",
        std::mem::size_of::<AuthTreeInternalNode>()
    );

}

type AKey = [u64; 4];
type ADigest = [u8; 224 / 8];
type Pointer = usize;

const NODE_CAPACITY: usize = 256;
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
            cache: HashMap::new(),
            data:  HashMap::new(),
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

            let mut target = self.cache.get_mut(pointer).unwrap();
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

    fn insert(&mut self, entry : AuthTreeEntry) {
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
            return;
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
                return
            }

            // Mutate existing entry
            if current_node.leaf && current_node.keys[index] == entry.key {
                let entry_pointer = current_node.pointers[index];
                *self.data.get_mut(&entry_pointer).unwrap() = entry;
                return
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
        let offset = if node.leaf { 0 } else { 1 };

        // Shift keys to the right
        node.keys.copy_within(index..node.elements, index + 1);
        node.keys[index] = *key;

        // Shift pointers to the right
        node.pointers
            .copy_within(index+offset..node.elements + offset, index + 1);
        node.pointers[index+offset] = new_pointer;

        // Shift digests to the right
        node.digests
            .copy_within(index+offset..node.elements + offset, index + 1);
        node.digests[index+offset] = *new_digest;

        node.elements += 1;

        return
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
        for idx in 0..self.elements {
            if key <= &self.keys[idx] {
                return idx;
            }
        }
        return self.elements;
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


#[derive(Debug)]
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

    #[test]
    fn insert_contains_not_contains() {

        const EXP : u64 = 1_000_000;
        let mut tree = TreeCache::new();

        let now = Instant::now();
        for num in 0..EXP {
            tree.insert(AuthTreeEntry::get_test_entry(2*num));
        }
        println!("Insert: {}ns", now.elapsed().as_nanos() / EXP as u128);

        let now = Instant::now();
        for num in 0..EXP {
            let res = tree.get(&[2*num; 4]);
            assert!(res.unwrap().key[0] == 2*num);
        }
        println!("Get Some: {}ns", now.elapsed().as_nanos() / EXP as u128);

        let now = Instant::now();
        for num in 0..EXP {
            let res = tree.get(&[2*num + 1; 4]);
            assert!(res.is_none());
        }
        println!("Get None: {}ns", now.elapsed().as_nanos() / EXP as u128);

        let now = Instant::now();
        println!("Nuber of blocks: {}", tree.cache.len());
        for num in 0..100 {
            tree.update_hashes();
        }
        println!("Update hashes: {}ms", now.elapsed().as_millis() / 100_u128);

    }
}
