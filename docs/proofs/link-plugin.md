# Rocq Link Plugin

This document describes the Rocq plugin used to factor repetitive link
definitions for Rust records and enums.

The plugin is loaded by `links.RocqOfRust`, so link files normally only need:

```coq
Require Import links.RocqOfRust.
```

## Commands

Use `RocqOfRustLinkEnum` inside a module to generate the local `t` type and the
standard link instances:

```coq
Module Ordering.
  RocqOfRustLinkEnum "core::cmp::Ordering" :=
  | Less
  | Equal
  | Greater
  .
End Ordering.
```

Use `RocqOfRustLinkRecord` for struct-like records:

```coq
Module Point.
  RocqOfRustLinkRecord "example::Point" := {
    x : Z;
    y : Z;
  }.
End Point.
```

The generated definitions include:

- `t`
- `IsLink`
- `IsOfTy`
- `IsOfValueWith...`
- `IsOfValue...`
- `SubPointer` definitions for fields

You can inspect the generated definitions with:

```coq
Print Module Ordering.
```

Enum variants can carry tuple-style or record-style fields:

```coq
Module Message.
  RocqOfRustLinkEnum "example::Message" :=
  | Ping
  | Write (bytes : list u8)
  | Move { x : Z; y : Z; }
  .
End Message.
```

Use `as "RustName"` when the Rocq constructor name must differ from the Rust
variant name:

```coq
Module Keyword.
  RocqOfRustLinkEnum "example::Keyword" :=
  | Type_ as "Type"
  .
End Keyword.
```

## Regression Test

The plugin has a print-based regression check:

```sh
cd RocqOfRust
make plugin-inline-print-check
```

This compiles `plugin/test_inline_print.v`, captures the output of selected
`Print` commands, and checks that the expected substrings in
`plugin/test_inline_print.expected` are present.

The test file is listed in `blacklist.txt`, because it intentionally emits
debug output and should not be part of the normal `make` build.
