# Repository Guidelines

## Project Structure & Module Organization

Hammer is a C99 parser-combinator library. `src/hammer.h` defines the public API;
`src/parsers/` implements combinators, `src/backends/` contains parsing engines,
and `src/bindings/` provides Python, Java, C++, and Go interfaces. C tests live in
`tests/`, including `tests/parsers/` and `tests/backends/`. `examples/` contains
protocol parsers; `docs/assets/` holds documentation images. Build logic lives in
`SConstruct` and `src/SConscript`; maintenance tools live in `tools/`.

## Build, Test, and Development Commands

Install GCC, SCons, pkg-config, and GLib development headers (`libglib2.0-dev` on
Ubuntu). Run commands from the repository root:

- `scons`: build optimized libraries and the test executable under `build/opt/`.
- `scons test`: build and run the core C suite.
- `scons --variant=debug test`: build and test with debugging symbols.
- `scons bindings=all test`: build and test all language bindings; see
  [DEVELOPMENT.md](DEVELOPMENT.md) for their dependencies.
- `scons bindings=python testpython`: test just the Python binding.
- `doxygen Doxyfile`: generate API documentation in `docs/html/`.
