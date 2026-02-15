# Testing revm_interpreter

This project uses Rocq compilation as the test runner.

## How tests are written

- Tests live in:
  - `revm/revm_interpreter/tests/`
  - `revm/revm_interpreter/instructions/tests/`
- A typical test is a `Goal` proved by computation:
  - `timeout 1 vm_compute.`
  - `reflexivity.`
- If a `Goal` no longer reduces to the expected value, the `.vo` build fails.

## Run tests

Build one test file:

```sh
make revm/revm_interpreter/instructions/tests/arithmetic.vo -j1
```

Build all current revm interpreter test files:

```sh
make -j1 \
  revm/revm_interpreter/tests/interpreter_types.vo \
  revm/revm_interpreter/tests/interpreter.vo \
  revm/revm_interpreter/tests/host.vo \
  revm/revm_interpreter/instructions/tests/arithmetic.vo \
  revm/revm_interpreter/instructions/tests/bitwise.vo \
  revm/revm_interpreter/instructions/tests/contract.vo
```

Notes:

- `make ... .vo` is the canonical workflow in this repo.
- If you changed Jinja templates (`*.v.jinja2`), run `make jinja` first.
- `-j1` is useful while debugging; increase parallelism when stable.

## Add a new test

1. Add a new `Goal` in an existing test file (or add a new file under one of the test directories).
2. Use `make path/to/test_file.vo` to compile and run it.
3. If adding a new file, ensure it is picked up by `_RocqProject`/`RocqMakefile` generation (run `make` once to regenerate if needed).
