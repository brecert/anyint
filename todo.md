- [x] Better type support so that `let x: int<i32, 2> = int::from_lossy(5);` works
      If `from_lossy` and similar is to remain const, other features may need to be implemented first like const fn in traits
- [~] A macro for writing int, so that `let x = n!(16u7);` is possible
  - better testing for said macro
  - possibly have it so that a value isn't needed so that `n![u7]::new(16)` is possible
  - possibly rename to `int` so that `int!(16, i7)` or `int!(16i7)` is possible
  - figure out better semantics and syntax for the macro
    proposed:
      ```rust
      int![u7]::new(21) // could be a type macro for use in many areas
      int!(u7, 21)
      int!(21u7)

      n![u7]::new(21)
      n!(u7, 21)
      n!(21u7) // 1 vote
      ```
- [~] More methods
- [ ] A more generic implementation once rust has better type support for that
- [~] FromStr and other implementations
- [ ] A Wrapped implementation
- [x] const fn in traits once rust supports that
- [~] feature flags
  - [x] no_std support
    - Need to look into if this can be improved
    - should have better testing
  - [~] num traits
- [ ] bigints or similar
- [~] better docs and doctests
- [ ] every one of these is fufilled: https://rust-lang.github.io/api-guidelines/documentation.html
- [~] very heavy cleanup
  - [~] test normalization and cleanup
  - [~] split up lib.rs
- [~] add benchmarks
  - [ ] bench all of the operators for comparative performance
  - [ ] fit performance within a set percentage of normal integers
- [ ] code coverage
