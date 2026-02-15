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
  revm/revm_interpreter/instructions/tests/block_info.vo \
  revm/revm_interpreter/instructions/tests/contract.vo \
  revm/revm_interpreter/instructions/tests/contract/call_helpers.vo \
  revm/revm_interpreter/instructions/tests/control.vo \
  revm/revm_interpreter/instructions/tests/stack.vo \
  revm/revm_interpreter/instructions/tests/system.vo \
  revm/revm_interpreter/instructions/tests/memory.vo
```

Notes:

- `make ... .vo` is the canonical workflow in this repo.
- If you changed Jinja templates (`*.v.jinja2`), run `make jinja` first.
- `-j1` is useful while debugging; increase parallelism when stable.

## Add a new test

1. Add a new `Goal` in an existing test file (or add a new file under one of the test directories).
2. Use `make path/to/test_file.vo` to compile and run it.
3. If adding a new file, ensure it is picked up by `_RocqProject`/`RocqMakefile` generation (run `make` once to regenerate if needed).

## Simulate coverage

Each simulate definition models one EVM instruction in Rocq. The table below tracks which ones have a smoke test (a `Goal` that reduces via `vm_compute`).

"Not testable" means the instruction uses an `Admitted` trait instance (e.g. `InputTraits`, `Host` getters) that prevents `vm_compute` from reducing.

### Arithmetic (`instructions/tests/arithmetic.v`)

| Instruction  | Simulate file | Tested |
|--------------|---------------|--------|
| add          | `arithmetic/add.v` | Yes |
| sub          | `arithmetic/sub.v` | Yes |
| mul          | `arithmetic/mul.v` | Yes |
| div          | `arithmetic/div.v` | Yes |
| rem          | `arithmetic/rem.v` | Yes |
| sdiv         | `arithmetic/sdiv.v` | Yes |
| smod         | `arithmetic/smod.v` | Yes |
| addmod       | `arithmetic/addmod.v` | Yes |
| mulmod       | `arithmetic/mulmod.v` | Yes |
| exp          | `arithmetic/exp.v` | Yes |
| signextend   | `arithmetic/signextend.v` | Yes |

### Bitwise (`instructions/tests/bitwise.v`)

| Instruction  | Simulate file | Tested |
|--------------|---------------|--------|
| lt           | `bitwise/lt.v` | Yes |
| gt           | `bitwise/gt.v` | Yes |
| eq           | `bitwise/eq.v` | Yes |
| slt          | `bitwise/slt.v` | Yes |
| sgt          | `bitwise/sgt.v` | Yes |
| bitand       | `bitwise/bitand.v` | Yes |
| bitor        | `bitwise/bitor.v` | Yes |
| bitxor       | `bitwise/bitxor.v` | Yes |
| iszero       | `bitwise/iszero.v` | Yes |
| not          | `bitwise/not.v` | Yes |
| byte         | `bitwise/byte.v` | Yes |
| shl          | `bitwise/shl.v` | Yes |
| shr          | `bitwise/shr.v` | Yes |
| sar          | `bitwise/sar.v` | Yes |

### Control (`instructions/tests/control.v`)

| Instruction    | Simulate file | Tested |
|----------------|---------------|--------|
| stop           | `control/stop.v` | Yes |
| invalid        | `control/invalid.v` | Yes |
| jump           | `control/jump.v` | No (uses `Jumps` - Admitted) |
| jumpi          | `control/jumpi.v` | No (uses `Jumps` - Admitted) |
| jump_inner     | `control/jump_inner.v` | No (uses `Jumps` - Admitted) |
| jumpdest_or_nop | `control/jumpdest_or_nop.v` | No (uses `Immediates` - Admitted) |
| pc             | `control/pc.v` | No (uses `LegacyBytecode` - Admitted) |
| ret            | `control/ret.v` | Yes |
| revert         | `control/revert.v` | Yes |
| return_inner   | `control/return_inner.v` | No (tested via ret/revert) |
| unknown        | `control/unknown.v` | Yes |

### Stack (`instructions/tests/stack.v`)

| Instruction  | Simulate file | Tested |
|--------------|---------------|--------|
| pop          | `stack/pop.v` | Yes |
| push0        | `stack/push0.v` | Yes |
| push         | `stack/push.v` | No (uses `Immediates` - Admitted) |
| dup          | `stack/dup.v` | Yes |
| swap         | `stack/swap.v` | Yes |

### System (`instructions/tests/system.v`)

| Instruction     | Simulate file | Tested |
|-----------------|---------------|--------|
| gas             | `system/gas.v` | Yes |
| address         | `system/address.v` | No (uses `InputTraits` - Admitted) |
| caller          | `system/caller.v` | No (uses `InputTraits` - Admitted) |
| callvalue       | `system/callvalue.v` | No (uses `InputTraits` - Admitted) |
| calldataload    | `system/calldataload.v` | No (uses `InputTraits` - Admitted) |
| calldatasize    | `system/calldatasize.v` | No (uses `InputTraits` - Admitted) |
| calldatacopy    | `system/calldatacopy.v` | No (uses `InputTraits` - Admitted) |
| codesize        | `system/codesize.v` | No (uses `LegacyBytecode` - Admitted) |
| codecopy        | `system/codecopy.v` | No (uses `LegacyBytecode` - Admitted) |
| returndatasize  | `system/returndatasize.v` | No (uses `ReturnData` - Admitted) |
| returndatacopy  | `system/returndatacopy.v` | No (uses `ReturnData` - Admitted) |
| keccak256       | `system/keccak256.v` | Yes |
| memory_resize   | `system/memory_resize.v` | No (helper, not an instruction) |

### Memory (`instructions/tests/memory.v`)

| Instruction  | Simulate file | Tested |
|--------------|---------------|--------|
| msize        | `memory/msize.v` | Yes |
| mstore       | `memory/mstore.v` | Yes |
| mload        | `memory/mload.v` | Yes |
| mstore8      | `memory/mstore8.v` | Yes |
| mcopy        | `memory/mcopy.v` | Yes |

### Contract (`instructions/tests/contract.v`)

| Instruction     | Simulate file | Tested |
|-----------------|---------------|--------|
| static_call     | `contract/static_call.v` | Yes |
| call            | `contract/call.v` | Yes (includes abstract-`is_static` branch check) |
| call_code       | `contract/call_code.v` | Yes |
| delegate_call   | `contract/delegate_call.v` | Yes |
| extcall_input   | `contract/extcall_input.v` | Yes (in `instructions/tests/contract/call_helpers.v`) |

### Contract Helpers (`instructions/tests/contract/call_helpers.v`)

| Helper function | Source file | Tested |
|-----------------|-------------|--------|
| extcall_input | `simulate/contract/extcall_input.v` | Yes |
| get_memory_input_and_out_ranges | `instructions/contract/simulate/call_helpers.v` | Yes |

### Host

| Instruction    | Simulate file | Tested |
|----------------|---------------|--------|
| balance        | `host/balance.v` | No (uses `InputTraits` - Admitted) |
| selfbalance    | `host/selfbalance.v` | No (uses `InputTraits` - Admitted) |
| blockhash      | `host/blockhash.v` | No (uses Host methods - Admitted) |
| sload          | `host/sload.v` | No (uses Host methods - Admitted) |
| sstore         | `host/sstore.v` | No (uses Host methods - Admitted) |
| tload          | `host/tload.v` | No (uses `InputTraits` - Admitted) |
| tstore         | `host/tstore.v` | No (uses `InputTraits` - Admitted) |
| log            | `host/log.v` | No (uses `InputTraits` - Admitted) |
| selfdestruct   | `host/selfdestruct.v` | No (uses `InputTraits` - Admitted) |
| extcodesize    | `host/extcodesize.v` | No (uses Host methods - Admitted) |
| extcodecopy    | `host/extcodecopy.v` | No (uses Host methods - Admitted) |
| extcodehash    | `host/extcodehash.v` | No (uses Host methods - Admitted) |

### Block Info (`instructions/tests/block_info.v`)

| Instruction   | Simulate file | Tested |
|---------------|---------------|--------|
| basefee       | `block_info/basefee.v` | Yes |
| blob_basefee  | `block_info/blob_basefee.v` | Yes |
| block_number  | `block_info/block_number.v` | Yes |
| coinbase      | `block_info/coinbase.v` | Yes |
| difficulty    | `block_info/difficulty.v` | Yes |
| gaslimit      | `block_info/gaslimit.v` | Yes |
| timestamp     | `block_info/timestamp.v` | Yes |
| chainid       | `block_info/chainid.v` | Yes |

### Tx Info

| Instruction  | Simulate file | Tested |
|--------------|---------------|--------|
| gasprice     | `tx_info/gasprice.v` | No (uses `TransactionGetter` - Admitted) |
