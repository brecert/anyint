extern crate test;
use crate::{integer::int, prelude::NonStandardIntegerCommon};
use test::{black_box, Bencher};

macro wrapping_bench($method:ident) {
    mod $method {
        use super::*;

        #[bench]
        fn int_u21(b: &mut Bencher) {
            b.iter(|| {
                (1..5000).fold(int::<u32, 21>::new(0), |old, new| {
                    black_box(old.$method(int::<u32, 21>::new(new)))
                })
            });
        }

        #[bench]
        fn std_u32(b: &mut Bencher) {
            b.iter(|| (1..5000).fold(0, |old: u32, new| black_box(old.$method(new))));
        }

        #[bench]
        fn int_i38(b: &mut Bencher) {
            b.iter(|| {
                (1..5000).fold(int::<i64, 38>::new(0), |old, new| {
                    black_box(old.$method(int::<i64, 38>::new(new)))
                })
            });
        }

        #[bench]
        fn std_i64(b: &mut Bencher) {
            b.iter(|| (1..5000).fold(0, |old: i64, new| black_box(old.$method(new))));
        }
    }
}

wrapping_bench!(wrapping_add);
wrapping_bench!(wrapping_sub);
wrapping_bench!(wrapping_mul);
wrapping_bench!(wrapping_div);
wrapping_bench!(wrapping_rem);
