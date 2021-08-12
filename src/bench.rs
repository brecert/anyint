extern crate test;
use crate::{integer::int, prelude::NonStandardIntegerCommon};
use test::{black_box, Bencher};

#[bench]
fn bench_add_5000_u21(b: &mut Bencher) {
    b.iter(|| {
        (0..5000).fold(int::<u32, 21>::new(0), |old, new| {
            black_box(old.wrapping_add(int::<u32, 21>::new(new)))
        })
    });
}

#[bench]
fn bench_add_5000_u32(b: &mut Bencher) {
    b.iter(|| (0..5000).fold(0, |old: u32, new| black_box(old.wrapping_add(new))));
}

#[bench]
fn bench_add_5000_i38(b: &mut Bencher) {
    b.iter(|| {
        (0..5000).fold(int::<i64, 38>::new(0), |old, new| {
            black_box(old.wrapping_add(int::<i64, 38>::new(new)))
        })
    });
}

#[bench]
fn bench_add_5000_i64(b: &mut Bencher) {
    b.iter(|| (0..5000).fold(0, |old: i64, new| black_box(old.wrapping_add(new))));
}
