# REVM Osaka simulations and tests

REVM has one executable transaction path: the typed Context, undo journal,
interpreter, frames and Handler. It follows the checked-in Rust structures,
integer types and control flow and reuses the canonical instruction simulations.
The old snapshot-based transaction executor and its exclusive fixture runners
have been removed.

The supported acceptance target is **14,614 Osaka state tests and 56 Osaka raw
transaction tests** from EEST `tests@v20.0.2` (commit
`abbe05777ab83fb94ce18c425daaa7ab79e779c1`). The cleaned executable passes both
complete selections, independently verified in
`target/revm-cleanup/state-verified.json` and `target/revm-cleanup/raw-verified.json`.
Pre-cleanup evidence remains under `target/osaka-context-v2/`.
Blockchain, Engine API and sync execution are outside this target.

The cleanup build passed all native specialization proofs and smoke checks, and
all 59 retained Rocq regression targets passed. The source audit preserves 105
proof-containing files unchanged and adds no admissions or axioms.

The fresh state run uses six fixed shards. The concurrent run recorded two
180-second timeouts (`return50000_2` and `static_return50000_2`); full isolated
reruns of shards 3 and 4 passed with the same executable and limits. Those cases
took 140.6 and 125.6 seconds in isolation. Original failures are retained under
`resumed-shards/`, and successful retry records are under `retry/`. The accepted
state evidence consists of original shards 0, 1, 2 and 5 plus retry shards 3 and 4.
`run-identity.json` records the executable and frozen harness hashes.
To recheck the accepted state evidence from the repository root:

```sh
python3 target/revm-cleanup/harness/verify_eest_corpus.py \
  --fixtures target/osaka-fixtures \
  --bridge target/revm-cleanup/native/native_transaction_bridge \
  --format state_test --fork Osaka \
  --results target/revm-cleanup/resumed-shards/state-{0,1,2,5}-results.jsonl \
            target/revm-cleanup/retry/state-{3,4}-results.jsonl
```

## Code map

Paths below are relative to `RocqOfRust/revm/`.

| Layer | Source |
| --- | --- |
| Typed accounts and storage | [revm_state/simulate/lib.v](../revm_state/simulate/lib.v) |
| Undo journal and checkpoints | [inner.v](../revm_context/journal/simulate/inner.v), [journal.v](../revm_context/simulate/journal.v) |
| Context and database-backed host | [context.v](../revm_context/simulate/context.v), [host.v](../revm_context/simulate/host.v) |
| Interpreter and instruction dispatch | [eth_interpreter.v](../revm_interpreter/simulate/eth_interpreter.v), [runtime.v](../revm_interpreter/simulate/runtime.v) |
| Call/create frames and execution loop | [frame.v](../revm_handler/simulate/frame.v), [evm.v](../revm_handler/simulate/evm.v) |
| Transaction preparation, execution and settlement | [handler.v](../revm_handler/simulate/handler.v), [pre_execution.v](../revm_handler/simulate/pre_execution.v), [post_execution.v](../revm_handler/simulate/post_execution.v) |
| Precompiles | [precompile_provider.v](../revm_handler/simulate/precompile_provider.v), [precompiles.v](../revm_precompile/simulate/precompiles.v) |
| Fixture records and conversion | [eest_types.v](../revm_handler/simulate/eest_types.v), [eest_context.v](../revm_handler/simulate/eest_context.v) |
| EEST transaction boundary | [eest_transaction.v](../revm_handler/simulate/eest_transaction.v) |

`EestTypes` owns the JSON-facing account, block, log, input and result records.
Fixture integers are validated before conversion to Rust types. `EestContext.run`
executes the typed handler. `EestTransaction.run` applies EEST's sender-nonce
boundary to that same executor. The JSONL protocol and its rejection/result
variants are unchanged.

State mutations use typed undo entries and checkpoints. The interpreter keeps
Rust's eight fields; the frame stack is a list. Fuel bounds evaluation separately
from Ethereum gas. Exhaustion and internal/database failures never become a
successful EVM result. Completed fixture accounts omit zero-valued storage slots,
including slots in untouched accounts. Rejected transactions retain input state.

Small historical fork checks remain where they follow Rust or support reusable
primitive tests. Osaka still supports legacy transaction and bytecode formats.
The old `simulations_legacy/gas.v` is a disabled historical proof source, retained
unchanged; it is not part of the executable or its dependency graph.

## Proof boundaries

Canonical instruction simulations, generic interpreter/dispatcher proofs and
Rust links remain in place. The typed runtime derives its instruction bodies
from those definitions: all 256 opcode routes and 28 host adapters have equality
proofs. Concrete executable primitives live in `simulate/eth_types.v`; the small
`tests/interpreter_types.v` export supports existing generic instruction tests.

The native generator specializes the canonical context, instructions, frames
and handler through `ContextLoad`, `ContextOwned`, `ContextHandlers`,
`ContextRuntime` and `NativeTransactions`. Rocq checks the specialization
equalities, including equality to `EestContext.run` and `EestTransaction.run`.
Extraction rejects computational axiom placeholders. Functional extensionality
appears only in erased proofs.

These proofs retain their existing assumptions. Neither passing EEST nor the
specialization equalities establish full equivalence of the handler to Rust.
Cryptographic routines execute Rocq definitions; native-provider correspondence
and general cryptographic correctness are not claimed.

## Review requirements for handwritten REVM changes

Before submitting changes, compare every new or modified semantic helper's
signature and arithmetic with its Rust counterpart. Use Rust integer types such
as `u8`, `u64`, `u128` and `usize`, including helper parameters and optional values;
typed record fields alone are not enough. Preserve checked, saturating and
wrapping operations explicitly. Fixture-facing `Z` values belong at the input
boundary, with validation and conversion kept there rather than inside semantic
helpers. Header randomness uses `B256`, not an integer substitute.

For numeric transaction tags, use `Z.eqb` conditionals rather than matching on
`Z` literals, following the extraction-performance review. Keep blank lines
between separate definitions, lemmas and examples. Review the whole changed path for each comment,
not only the line GitHub highlights.

These requirements track Clarus's recurring Rust-type and spacing feedback,
including the [integer-parameter comment on #1012](https://github.com/formal-land/rocq-of-rust/pull/1012#discussion_r4291942653)
and the [numeric-dispatch comment on #1012](https://github.com/formal-land/rocq-of-rust/pull/1012#discussion_r4291906682).

## Build and focused checks

Activate the Rocq/OCaml toolchain and install the project's dependencies,
OCaml `yojson` and `zarith`, and Python `jinja2` and `pycryptodome`. From
`RocqOfRust`:

```sh
OCAMLRUNPARAM=d=1 bash revm/tests/run_fixture_tests.sh
OCAMLRUNPARAM=d=1 python3 revm/tests/native/build.py \
  --numeric-backend zarith --native-memory-limit-mib 8192 \
  --output-dir ../target/revm-cleanup/native --smoke --bridge
```

The script runs standalone harness checks and retained Rocq regression targets.
They cover canonical instructions, typed accounts/journals, database failures,
cold/warm accesses, nested reverts, creation collisions, fees/refunds, EIP-7702,
precompiles, authentication/validation helpers and state/log commitments.
Transaction and creation smoke inputs live in `revm_handler/tests/transaction_cases.v`;
they have no dependency on a second executor.

The builder refreshes canonical dependencies with `make -j1`, compiles all native
specialization proofs, checks extraction, and runs transaction, creation,
authorization, cryptographic and numeric smoke executables. Generated sources,
proofs, OCaml files and logs stay in the selected ignored output directory.

Use one compiler job. Rocq compilation and executable tests use a 2 GiB
address-space cap. Native OCaml compilation has a separate 8192 MiB allowance.
On OCaml 5.5, `OCAMLRUNPARAM=d=1` keeps the single-domain runtime within the cap.
Use a timeout and record peak RSS for computation checks.

The optional historical instruction/parser/comparison tests require a separate
`ethereum/tests` GeneralStateTests snapshot. Set `REVM_FIXTURE_ROOT` to run them;
they do not contribute to the Osaka acceptance counts. The unchanged
`revm_handler/tests/transaction_auth.v` signature computation examples previously
exceeded a 3600-second wall limit without an assertion failure. They remain
available with `REVM_SLOW_TESTS=1`; native authentication and all Osaka raw
transaction tests are required independently of that supplementary check.

`--reuse` reuses a native build only when source/toolchain/options and output
hashes match; requested smoke executables still run. The default and `--no-cache`
rebuild. Reuse assumes installed dependencies have not changed without a version
change. Use a fresh output directory for acceptance evidence.

## Run and independently verify Osaka

The local pinned fixture root is `target/osaka-fixtures`. To obtain another copy,
use `acquire_osaka_fixtures.py`; the corpus runner itself does not download data.
From the repository root, using the newly built bridge:

```sh
OCAMLRUNPARAM=d=1 python3 RocqOfRust/revm/tests/run_eest_corpus.py \
  --fixtures target/osaka-fixtures \
  --bridge target/revm-cleanup/native/native_transaction_bridge \
  --format state_test --fork Osaka --fuel 2000000 --timeout 180 \
  --results target/revm-cleanup/state-results.jsonl \
  --summary target/revm-cleanup/state-summary.json
python3 RocqOfRust/revm/tests/verify_eest_corpus.py \
  --fixtures target/osaka-fixtures \
  --bridge target/revm-cleanup/native/native_transaction_bridge \
  --format state_test --fork Osaka \
  --results target/revm-cleanup/state-results.jsonl

OCAMLRUNPARAM=d=1 python3 RocqOfRust/revm/tests/run_eest_corpus.py \
  --fixtures target/osaka-fixtures \
  --bridge target/revm-cleanup/native/native_transaction_bridge \
  --format transaction_test --fork Osaka --fuel 2000000 --timeout 180 \
  --results target/revm-cleanup/raw-results.jsonl \
  --summary target/revm-cleanup/raw-summary.json
python3 RocqOfRust/revm/tests/verify_eest_corpus.py \
  --fixtures target/osaka-fixtures \
  --bridge target/revm-cleanup/native/native_transaction_bridge \
  --format transaction_test --fork Osaka \
  --results target/revm-cleanup/raw-results.jsonl
```

Use new result paths for a new executable or harness. Acceptance requires
`all_selected_pass: true` with exactly 14,614 state cases and 56 raw transaction
cases. The complete-all-forks flags describe different selections and need not
be true for an Osaka pass. A saved pass label alone is insufficient: the verifier
reconstructs requests and comparisons from the pinned fixtures and native outputs,
checks exact identities, and rejects missing, duplicate or mixed-run records.

State requests execute signed transactions recovered by Rocq. Comparisons include
full account state, logs, gas, authentication and Rocq-computed state/log
commitments. Expected rejections require the mapped reason, unchanged state and
appropriate commitments. Raw transaction requests validate exact signed bytes;
positive results must match sender, transaction hash and intrinsic gas, while
negative results require a definite rejection. Unsupported, incomplete, failed
or timed-out execution cannot count as an expected rejection.

The loader validates pinned metadata, format/fork census, exact case IDs and
fixture payload hashes. The Osaka adapter supplies the six-blob transaction cap.
Its BLOCKHASH fallback uses Keccak-256 of the signed 64-bit block number in
decimal, matching the state-test environment. These policies stay at the fixture
boundary.

Each bridge process has the existing 2 GiB limit. Use two million fuel and a
180-second wall deadline per case. Keep compilation idle during corpus runs:
the large static-return case previously took 179.2 seconds under these limits.
Original failures and any fresh retry evidence must both be retained.

### Resume, shards and CI

`--shard-index` and `--shard-count` select deterministic partitions. The verifier
accepts multiple result files and requires exact coverage of the selected set.
`--resume` continues an interrupted result file using its `.manifest.json` sidecar.
The manifest binds the fixture pin, selection, bridge and harness digests, fuel
and timeout. Completed records are independently checked before skipping them;
a partial last line is retried. Complete failures are retained, so resumption
is not a semantic retry. Changed execution settings require fresh result paths.

The manual **REVM Osaka inventory** workflow builds one executable and checks the
same two selections in 16 shards, with at most two jobs running together. Pull
requests run lightweight harness checks. Re-running failed jobs in the same run
uses retained artifacts/checkpoints; starting a new run creates new evidence.
Artifact retention is 14 days, and hard cancellation can lose the latest upload.

`run_eest_stream.py` offers bounded-disk archive processing through the same
runner/verifier. Its compact receipts attest to local comparisons; hashes alone
cannot independently recheck discarded native outputs. `--resume --replay`
executes the retained selection again. The full archive includes unsupported
blockchain/Engine/sync formats, so its inventory is not an all-EEST pass.

## Numeric extraction trust boundary

The default backend is inductive extraction. `--numeric-backend zarith` uses
Stdlib's explicitly uncertified OCaml/Zarith mappings for positive, N and Z;
nat remains inductive. Neither backend replaces EVM or cryptographic algorithms
with an external provider. Build backends in separate output directories when
comparing them.

Guarded shifts preserve sign extension for enormous right shifts and zero for
zero left shifts. Unrepresentable nonzero left shifts fail as resource errors.
Guarded powers preserve `Z.pow` behavior for negative/zero exponents and huge
exponents with bases zero or ±1; other unrepresentable computations fail.
Signed division, remainder and zero divisors retain Stdlib semantics.

Native numeric smoke checks compare 84 power and 168 shift cases against
Rocq-computed references and check huge-count boundaries. The arithmetic mappings
still trust the OCaml/Zarith runtime. `FixedBytes.bytes_be` has a separate Rocq
proof equating its shift/mask implementation with the division-based definition;
that proof does not certify the extracted arithmetic runtime.
