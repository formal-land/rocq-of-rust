# Simulate Instructions

Formal verification of the EVM instruction simulation. Each instruction has a `simulate` definition and a proof that it matches the `run` (translated) definition.

- ✓ = fully proven (`Qed`)
- ✗ = admitted (`Admitted`)

Some entries are helper functions used by other instructions rather than standalone EVM opcodes (e.g., `jump_inner`, `return_inner`, `extcall_input`, `memory_resize`).

## arithmetic/
Rust source: [`../arithmetic.rs`](../arithmetic.rs)

| Instruction | Status |
|---|:---:|
| [add](arithmetic/add.v) | ✓ |
| [addmod](arithmetic/addmod.v) | ✓ |
| [div](arithmetic/div.v) | ✓ |
| [exp](arithmetic/exp.v) | ✓ |
| [mul](arithmetic/mul.v) | ✓ |
| [mulmod](arithmetic/mulmod.v) | ✓ |
| [rem](arithmetic/rem.v) | ✓ |
| [sdiv](arithmetic/sdiv.v) | ✓ |
| [signextend](arithmetic/signextend.v) | ✓ |
| [smod](arithmetic/smod.v) | ✓ |
| [sub](arithmetic/sub.v) | ✓ |

## bitwise/
Rust source: [`../bitwise.rs`](../bitwise.rs)

| Instruction | Status |
|---|:---:|
| [bitand](bitwise/bitand.v) | ✓ |
| [bitor](bitwise/bitor.v) | ✓ |
| [bitxor](bitwise/bitxor.v) | ✓ |
| [byte](bitwise/byte.v) | ✓ |
| [eq](bitwise/eq.v) | ✓ |
| [gt](bitwise/gt.v) | ✓ |
| [iszero](bitwise/iszero.v) | ✓ |
| [lt](bitwise/lt.v) | ✓ |
| [not](bitwise/not.v) | ✓ |
| [sar](bitwise/sar.v) | ✓ |
| [sgt](bitwise/sgt.v) | ✓ |
| [shl](bitwise/shl.v) | ✓ |
| [shr](bitwise/shr.v) | ✓ |
| [slt](bitwise/slt.v) | ✓ |

## block_info/
Rust source: [`../block_info.rs`](../block_info.rs)

| Instruction | Status |
|---|:---:|
| [basefee](block_info/basefee.v) | ✓ |
| [blob_basefee](block_info/blob_basefee.v) | ✓ |
| [block_number](block_info/block_number.v) | ✓ |
| [chainid](block_info/chainid.v) | ✓ |
| [coinbase](block_info/coinbase.v) | ✓ |
| [difficulty](block_info/difficulty.v) | ✓ |
| [gaslimit](block_info/gaslimit.v) | ✓ |
| [timestamp](block_info/timestamp.v) | ✓ |

## contract/
Rust source: [`../contract.rs`](../contract.rs)

| Instruction | Status |
|---|:---:|
| [call](contract/call.v) | ✓ |
| [call_code](contract/call_code.v) | ✓ |
| [delegate_call](contract/delegate_call.v) | ✓ |
| [extcall_input](contract/extcall_input.v) | ✓ |
| [static_call](contract/static_call.v) | ✓ |

## control/
Rust source: [`../control.rs`](../control.rs)

| Instruction | Status |
|---|:---:|
| [invalid](control/invalid.v) | ✓ |
| [jump](control/jump.v) | ✓ |
| [jump_inner](control/jump_inner.v) | ✓ |
| [jumpdest](control/jumpdest.v) | ✓ |
| [jumpi](control/jumpi.v) | ✓ |
| [pc](control/pc.v) | ✓ |
| [ret](control/ret.v) | ✓ |
| [return_inner](control/return_inner.v) | ✓ |
| [revert](control/revert.v) | ✓ |
| [stop](control/stop.v) | ✓ |
| [unknown](control/unknown.v) | ✓ |

## host/
Rust source: [`../host.rs`](../host.rs)

| Instruction | Status |
|---|:---:|
| [balance](host/balance.v) | ✓ |
| [blockhash](host/blockhash.v) | ✓ |
| [extcodecopy](host/extcodecopy.v) | ✓ |
| [extcodehash](host/extcodehash.v) | ✓ |
| [extcodesize](host/extcodesize.v) | ✓ |
| [log](host/log.v) | ✗ |
| [selfdestruct](host/selfdestruct.v) | ✗ |
| [selfbalance](host/selfbalance.v) | ✓ |
| [sload](host/sload.v) | ✓ |
| [sstore](host/sstore.v) | ✓ |
| [tload](host/tload.v) | ✓ |
| [tstore](host/tstore.v) | ✓ |

## memory/
Rust source: [`../memory.rs`](../memory.rs)

| Instruction | Status |
|---|:---:|
| [mcopy](memory/mcopy.v) | ✓ |
| [mload](memory/mload.v) | ✓ |
| [msize](memory/msize.v) | ✓ |
| [mstore](memory/mstore.v) | ✓ |
| [mstore8](memory/mstore8.v) | ✓ |

## stack/
Rust source: [`../stack.rs`](../stack.rs)

| Instruction | Status |
|---|:---:|
| [dup](stack/dup.v) | ✓ |
| [pop](stack/pop.v) | ✓ |
| [push](stack/push.v) | ✓ |
| [push0](stack/push0.v) | ✓ |
| [swap](stack/swap.v) | ✓ |

## system/
Rust source: [`../system.rs`](../system.rs)

| Instruction | Status |
|---|:---:|
| [address](system/address.v) | ✓ |
| [calldatacopy](system/calldatacopy.v) | ✓ |
| [calldataload](system/calldataload.v) | ✗ |
| [calldatasize](system/calldatasize.v) | ✓ |
| [caller](system/caller.v) | ✓ |
| [callvalue](system/callvalue.v) | ✓ |
| [codecopy](system/codecopy.v) | ✓ |
| [codesize](system/codesize.v) | ✓ |
| [gas](system/gas.v) | ✓ |
| [keccak256](system/keccak256.v) | ✓ |
| [memory_resize](system/memory_resize.v) | ✓ |
| [returndatacopy](system/returndatacopy.v) | ✓ |
| [returndatasize](system/returndatasize.v) | ✓ |

## tx_info/
Rust source: [`../tx_info.rs`](../tx_info.rs)

| Instruction | Status |
|---|:---:|
| [blob_hash](tx_info/blob_hash.v) | ✓ |
| [gasprice](tx_info/gasprice.v) | ✓ |
| [origin](tx_info/origin.v) | ✓ |

## Summary

| Category | Proven | Admitted | Total |
|---|:---:|:---:|:---:|
| arithmetic | 11 | 0 | 11 |
| bitwise | 14 | 0 | 14 |
| block_info | 8 | 0 | 8 |
| contract | 5 | 0 | 5 |
| control | 11 | 0 | 11 |
| host | 10 | 2 | 12 |
| memory | 5 | 0 | 5 |
| stack | 5 | 0 | 5 |
| system | 12 | 1 | 13 |
| tx_info | 3 | 0 | 3 |
| **Total** | **82** | **5** | **87** |
