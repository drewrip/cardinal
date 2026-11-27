# Documentation

- The root `README.md` should stay terse. Only include basic usage instructions. Do not include other documentation or explanation. Those should be clear from the rust docs.
- Keep the rust docs up to date. They should be concise and clear.

# Commits

- Keep commit messages terse: at most two sentences.
- Do not commit plan files unless explicitly asked.

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
