use super::*;
use std::time::Instant;

#[test]
fn endianness_to_ord() {
    for x in 500..600 {
        let x100 = get_test_entry(x);
        let x200 = get_test_entry(x + 1);
        assert!(x100.key < x200.key);
    }
}

#[test]
fn construct_leaf_simple() {
    let x: Vec<AuthElement> = (0..1000).map(|num| get_test_entry(num)).collect();
    let entry = AuthTreeInternalNode::new(
        true,
        [MIN_KEY, MAX_KEY],
        &mut x.iter().peekable(),
        NODE_CAPACITY,
    );

    assert!(entry.elements == NODE_CAPACITY);

    // println!("{:?} {:?}", entry.bounds[1], get_test_entry(NODE_CAPACITY-1).key);
    assert!(entry.bounds[1] >= get_test_entry(NODE_CAPACITY - 1).key);
}

#[test]
fn construct_leaf_with_max() {
    let x: Vec<AuthElement> = (0..NODE_CAPACITY * 2)
        .map(|num| get_test_entry(num))
        .collect();
    let entry = AuthTreeInternalNode::new(
        true,
        [MIN_KEY, get_test_entry(NODE_CAPACITY / 2).key],
        &mut x.iter().peekable(),
        NODE_CAPACITY,
    );

    assert!(entry.elements == 1 + NODE_CAPACITY / 2);
    assert!(entry.bounds[1] == get_test_entry(NODE_CAPACITY / 2).key);
}

#[test]
fn construct_two_leaf_with_max() {
    let x: Vec<AuthElement> = (0..NODE_CAPACITY * 5)
        .map(|num| get_test_entry(num))
        .collect();
    let entry = AuthTreeInternalNode::new(
        true,
        [MIN_KEY, MAX_KEY],
        &mut x.iter().peekable(),
        NODE_CAPACITY / 2,
    );

    assert!(entry.elements == NODE_CAPACITY / 2);

    let _entry = AuthTreeInternalNode::new(
        true,
        [MIN_KEY, MAX_KEY],
        &mut x.iter().peekable(),
        NODE_CAPACITY / 2,
    );
}

#[test]
fn construct_leaf_with_merge_simple() {
    let x: Vec<AuthElement> = (0..NODE_CAPACITY * 10)
        .map(|num| get_test_entry(num))
        .collect();
    let mut iter = x.iter().peekable();
    let mut entry = AuthTreeInternalNode::new(true, [MIN_KEY, MAX_KEY], &mut iter, NODE_CAPACITY);

    entry.bounds = [MIN_KEY, MAX_KEY];

    let x: Vec<AuthOp> = (NODE_CAPACITY..NODE_CAPACITY * 10)
        .map(|num| AuthOp::Insert(get_test_entry(num)))
        .collect();
    let mut iter = x.iter().peekable();

    let mut returns = Vec::new();
    let mut spares = Vec::new();
    // println!("START {:?}", entry);
    entry.merge_into_leaf(&mut returns, &mut spares, &mut iter);

    // println!("RET({}) {:?}", returns.len(), returns);
    assert!(returns.len() > 0);
}

#[test]
fn construct_leaf_with_merge_empty_start() {
    let x: Vec<AuthOp> = (0..100)
        .map(|num| AuthOp::Insert(get_test_entry(num)))
        .collect();
    let mut iter = x.iter().peekable();

    let mut entry = AuthTreeInternalNode::empty(true, [MIN_KEY, MAX_KEY]);

    entry.bounds = [MIN_KEY, MAX_KEY];

    let mut returns = Vec::new();
    let mut spares = Vec::new();
    // println!("START {:?}", entry);
    entry.merge_into_leaf(&mut returns, &mut spares, &mut iter);

    // println!("RET({}) {:?}", returns.len(), returns);
    assert!(returns.len() > 0);
}

#[test]
fn test_walk() {
    const EXP: usize = 20;
    let found: Vec<AuthOp> = (0..EXP)
        .map(|num| AuthOp::Insert(get_test_entry(num)))
        .collect();

    // Build tree
    let mut tree = TreeCache::new();
    tree.update_with_elements(&found);

    // Ensure all elements are there
    assert!(tree.walk().len() == EXP);
    tree.walk()
        .iter()
        .zip(found.clone())
        .for_each(|(elem, base_truth)| {
            assert!(elem.pointer == base_truth.unwrap_insert().pointer);
        });

    // Update tree
    let new_found: Vec<AuthOp> = (0..EXP)
        .map(|num| {
            let mut elem = get_test_entry(num);
            elem.pointer += 1_000_000;
            AuthOp::Insert(elem)
        })
        .collect();

    // Reuse tree
    tree.update_with_elements(&new_found);

    assert!(tree.walk().len() == EXP);
    tree.walk()
        .iter()
        .zip(found.clone())
        .for_each(|(elem, base_truth)| {
            assert!(elem.pointer == 1_000_000 + base_truth.unwrap_insert().pointer);
        });
}

#[test]
fn test_delete() {
    const EXP: usize = 1_000;
    let found: Vec<AuthOp> = (0..EXP)
        .map(|num| AuthOp::Insert(get_test_entry(num)))
        .collect();
    let delete: Vec<AuthOp> = (0..EXP)
        .map(|num| AuthOp::Delete(get_test_entry(2 * num + 1).key))
        .collect();

    // Build tree
    let mut tree = TreeCache::new();
    tree.update_with_elements(&found);

    // Check all are in
    for key_exists in &found {
        match tree.get(&key_exists.key(), &mut None) {
            GetPointer::Found(x) => assert!(x == key_exists.unwrap_insert().pointer),
            _ => panic!("Should find the key."),
        }
    }

    tree.update_with_elements(&delete);

    // Check all are in
    for (i, key_exists) in found.iter().enumerate() {
        match tree.get(&key_exists.key(), &mut None) {
            GetPointer::Found(_x) => assert!(i % 2 == 0),
            GetPointer::NotFound => assert!(i % 2 == 1),
            _ => panic!("Should find / not find the key."),
        }
    }

    let delete_all: Vec<AuthOp> = (0..EXP)
        .map(|num| AuthOp::Delete(get_test_entry(num).key))
        .collect();
    tree.update_with_elements(&delete_all);

    // All blocks were deleted
    assert!(tree.cache.len() == 0);
}

#[test]
fn test_gets() {
    const EXP: usize = 1_000;
    let found: Vec<AuthOp> = (0..EXP)
        .map(|num| AuthOp::Insert(get_test_entry(2 * num)))
        .collect();
    let notfound: Vec<AuthOp> = (0..EXP)
        .map(|num| AuthOp::Insert(get_test_entry(2 * num + 1)))
        .collect();

    // Build tree
    let mut tree = TreeCache::new();
    tree.update_with_elements(&found);

    // Ensure all elements are there
    assert!(tree.walk().len() == 1000);

    tree.get(&get_test_entry(390).key, &mut None);

    for key_exists in &found {
        match tree.get(&key_exists.key(), &mut None) {
            GetPointer::Found(x) => assert!(x == key_exists.unwrap_insert().pointer),
            _ => panic!("Should find the key."),
        }
    }

    for key_not_exists in &notfound {
        match tree.get(&key_not_exists.key(), &mut None) {
            GetPointer::NotFound => {}
            _ => panic!("Should NOT find the key."),
        }
    }

    // Update tree

    // Reuse tree
    tree.update_with_elements(&found);

    assert!(tree.walk().len() == 1000);

    for key_exists in &found {
        match tree.get(&key_exists.key(), &mut None) {
            GetPointer::Found(x) => assert!(x == key_exists.unwrap_insert().pointer),
            _ => panic!("Should find the key."),
        }
    }

    for key_not_exists in &notfound {
        match tree.get(&key_not_exists.key(), &mut None) {
            GetPointer::NotFound => {}
            _ => panic!("Should NOT find the key."),
        }
    }
}

#[test]
fn construct_tree() {
    const EXP: usize = 1_000_000;
    let x: Vec<AuthOp> = (0..EXP)
        .map(|num| AuthOp::Insert(get_test_entry(num)))
        .collect();

    let now = Instant::now();
    let mut tree = TreeCache::new();
    tree.update_with_elements(&x);
    let dur = now.elapsed();
    println!(
        "   Make Tree: Branches {}. {}ns\ttotal: {}ms",
        tree.cache.len(),
        dur.as_nanos() / EXP as u128,
        dur.as_millis()
    );

    assert!(tree.get_updated_pointers().len() == 0);

    // Cost of second update
    let now = Instant::now();
    // Reuse tree
    let removed = tree.update_with_elements(&x);
    let dur = now.elapsed();
    println!(
        "Update Tree: Branches {}. {}ns\ttotal: {}ms",
        tree.cache.len(),
        dur.as_nanos() / EXP as u128,
        dur.as_millis()
    );

    // Check internal book-keeping
    assert!(tree.get_updated_pointers().len() > 0);
    tree.clear_updated_pointers();
    assert!(tree.get_updated_pointers().len() == 0);
    for r in removed {
        assert!(!tree.cache.contains_key(&r));
    }

    // Cost of second update
    let now = Instant::now();
    // Reuse tree
    tree.update_with_elements(&x);
    let dur = now.elapsed();
    println!(
        "Update Tree: Branches {}. {}ns\ttotal: {}ms",
        tree.cache.len(),
        dur.as_nanos() / EXP as u128,
        dur.as_millis()
    );

    assert!(tree.get_updated_pointers().len() > 0);
}
