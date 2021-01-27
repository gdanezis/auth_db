use rayon::prelude::*;

use std::collections::HashMap;
use std::iter::Iterator;
use std::iter::Peekable;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::Instant;
use tiny_keccak::{Hasher, Sha3};

use parking_lot::Mutex;

pub mod auth_db;
use auth_db::*;

fn main() {
    rayon::ThreadPoolBuilder::new()
        .thread_name(|index| format!("rayon-global-{}", index))
        .build_global()
        .expect("Failed to build rayon global thread pool.");

    const EXP: usize = 1_000_000;
    let x: Vec<AuthOp> = (0..EXP)
        .map(|num| AuthOp::Insert(get_test_entry(num)))
        .collect();

    let now = Instant::now();
    let mut tree = TreeCache::new();
    tree.update_with_elements(&x);
    let dur = now.elapsed();
    println!(
        "  Make Tree: Branches {}. {}ns\ttotal: {}ms",
        tree.cache.len(),
        dur.as_nanos() / EXP as u128,
        dur.as_millis()
    );

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
}

#[cfg(test)]
pub(crate) mod tests;
