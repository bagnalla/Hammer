# Repository Guidelines

## Project Structure & Module Organization

- `src/` contains the C library: `hammer.h` exposes the API, `parsers/` implements combinators, `backends/` implements parsing engines, and `bindings/` contains language wrappers.
- `tests/` holds C tests, grouped under `parsers/` and `backends/` with shared infrastructure.
- `rusthammer/` contains the experimental Rust core: `src/grammar/`, feature-oriented `tests/`, runnable `examples/`, and Lean specifications/proofs under `lean/`.
- `examples/` contains C demos and protocol fixtures; `docs/assets/` contains documentation assets. `tools/` provides development utilities, and `plans/` records RustHammer designs.

## Build, Test, and Development Commands

C prerequisites are GCC, SCons, pkg-config, and GLib development headers. From the repository root:

- `scons` builds optimized libraries under `build/opt/`.
- `scons --variant=debug test` builds and runs the C suite with debug symbols.
- `scons bindings=all test` tests the library and bindings; install binding-specific dependencies listed in `DEVELOPMENT.md`.
- `doxygen Doxyfile` generates documentation under `docs/html/`.

From `rusthammer/`, use the pinned Rust toolchain:

- `cargo test --no-default-features` and `cargo test --features alloc` exercise both allocation configurations.
- `cargo run --example flags` runs a sample grammar.
- `python3 tools/verify.py --aeneas-dir /path/to/aeneas` checks formatting, tests, extraction, and Lean proofs; matching Aeneas/Charon revisions are required.
