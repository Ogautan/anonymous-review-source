#![allow(dead_code)]

use std::sync::atomic::{AtomicU64, Ordering};

struct Counter {
    value: AtomicU64,
}

impl Counter {
    fn new() -> Self {
        Self {
            value: AtomicU64::new(0),
        }
    }

    // Test case 1: High-frequency write in loop (should trigger sibling_arrays)
    fn increment_loop(&self) {
        for _ in 0..1_000_000 {
            self.value.fetch_add(1, Ordering::Relaxed);
        }
    }

    // Test case 2: Single read should not become hot_in_project.
    fn read_once(&self) -> u64 {
        self.value.load(Ordering::Relaxed)
    }

    // Test case 3: Single write has lower confidence than hot concurrent writes.
    fn write_once(&self) {
        self.value.store(42, Ordering::Relaxed);
    }
}

struct Stats {
    hits: AtomicU64,
    misses: AtomicU64,
}

impl Stats {
    fn new() -> Self {
        Self {
            hits: AtomicU64::new(0),
            misses: AtomicU64::new(0),
        }
    }

    // Test case 4: Multiple fields in same cache line with writes
    fn record_hit(&self) {
        self.hits.fetch_add(1, Ordering::Relaxed);
    }

    fn record_miss(&self) {
        self.misses.fetch_add(1, Ordering::Relaxed);
    }
}

// Test case 5: Nested loop (should have very high hotness score)
struct Matrix {
    data: Vec<AtomicU64>,
}

impl Matrix {
    fn process(&self) {
        for i in 0..100 {
            for j in 0..1000 {
                self.data[i * 1000 + j].fetch_add(1, Ordering::Relaxed);
            }
        }
    }
}
