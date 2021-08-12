extern crate test;
use crate::integer::int;
use test::Bencher;

#[bench]
fn bench_add_5000_u21(b: &mut Bencher) {
    b.iter(|| {
        (0..5000).fold(int::<u32, 21>::new(0), |old, new| {
            test::black_box(old + int::<u32, 21>::new(new))
        })
    });
}

#[bench]
fn bench_add_5000_u32(b: &mut Bencher) {
    b.iter(|| {
        (0..5000u32).fold(0, |old, new| {
            test::black_box(old + new)
        })
    });
}

#[bench]
fn bench_add_5000_i38(b: &mut Bencher) {
    b.iter(|| {
        (0..5000).fold(int::<i64, 38>::new(0), |old, new| {
            test::black_box(old + int::<i64, 38>::new(new))
        })
    });
}

#[bench]
fn bench_add_5000_i64(b: &mut Bencher) {
    b.iter(|| {
        (0..5000i64).fold(0, |old, new| {
            test::black_box(old + new)
        })
    });
}