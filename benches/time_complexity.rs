use std::collections::BinaryHeap;

use criterion::{black_box, criterion_group, criterion_main, BatchSize, Criterion};
use fibonacii_heap::Heap;

fn fill_fib_heap(size: usize) -> Heap<usize> {
    let mut heap = Heap::new();
    for i in 0usize..1 << size {
        heap.push(black_box(i.reverse_bits()));
    }
    heap
}

fn fill_bin_heap(size: usize) -> BinaryHeap<usize> {
    let mut heap = BinaryHeap::new();
    for i in 0usize..1 << size {
        heap.push(black_box(i.reverse_bits()));
    }
    heap
}

static SIZES: &[usize] = &[10, 11, 12, 13];

pub fn fibonacii_heap_benchmark(c: &mut Criterion) {
    let mut insert = c.benchmark_group("fibonacii/insert");
    for size in SIZES {
        insert.bench_function(format!("{size}"), |b| b.iter(|| fill_fib_heap(*size)));
    }
    insert.finish();

    let mut pop = c.benchmark_group("fibonacii/pop");
    for size in SIZES {
        pop.bench_function(format!("{size}"), |b| {
            b.iter_batched_ref(
                || fill_fib_heap(*size),
                |heap| {
                    while heap.pop().is_some() {}
                },
                BatchSize::SmallInput,
            )
        });
    }
    pop.finish();

    let mut pop1 = c.benchmark_group("fibonacii/pop1");
    for size in SIZES {
        pop1.bench_function(format!("{size}"), |b| {
            b.iter_batched_ref(|| fill_fib_heap(*size), Heap::pop, BatchSize::SmallInput)
        });
    }
    pop1.finish();
}

pub fn binary_heap_benchmark(c: &mut Criterion) {
    let mut insert = c.benchmark_group("binary/insert");
    for size in SIZES {
        insert.bench_function(format!("{size}"), |b| b.iter(|| fill_bin_heap(*size)));
    }
    insert.finish();

    let mut pop = c.benchmark_group("binary/pop");
    for size in SIZES {
        pop.bench_function(format!("{size}"), |b| {
            b.iter_batched_ref(
                || fill_bin_heap(*size),
                |heap| {
                    while heap.pop().is_some() {}
                },
                BatchSize::SmallInput,
            )
        });
    }
    pop.finish();

    let mut pop1 = c.benchmark_group("binary/pop1");
    for size in SIZES {
        pop1.bench_function(format!("{size}"), |b| {
            b.iter_batched_ref(
                || fill_bin_heap(*size),
                BinaryHeap::pop,
                BatchSize::SmallInput,
            )
        });
    }
    pop1.finish();
}

criterion_group!(fibonacii_heap, fibonacii_heap_benchmark);
criterion_group!(binary_heap, binary_heap_benchmark);
criterion_main!(fibonacii_heap, binary_heap);
