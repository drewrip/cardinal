# Testing

- Do not run the whole test suite (`cargo test`, `cargo test --workspace`):
  it takes too long. Run only what a change needs:
  - `cargo build` (and `cargo build -p <crate>` for dependent crates such
    as `cardinal-cli`) to check that everything compiles;
  - the test files that a change touches, or that exercise the code
    changed: `cargo test --test <file>`, narrowed by a name filter where
    one test is enough.
- If a test fails, check whether it also fails on the base commit before
  treating it as a regression.
