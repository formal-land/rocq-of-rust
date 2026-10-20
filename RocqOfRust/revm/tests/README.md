# REVM reference-fixture tests

This directory owns the executable REVM fixture harness. It can run from a
standalone rocq-of-rust checkout; no go-ethereum-fork modules are imported.
The tests compile temporary Rocq computation goals against the handwritten
REVM instruction simulations and concrete host/frame implementation.

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

From `RocqOfRust`, with the Rocq toolchain active and Python's `jinja2` and
`pycryptodome` available:

```sh
REVM_FIXTURE_ROOT=/path/to/GeneralStateTests \
  REVM_TEST_FORKS="Cancun Prague Osaka" MAKEFLAGS=-j1 \
  bash revm/tests/run_fixture_tests.sh
```

`REVM_FIXTURE_ROOT` must reference `GeneralStateTests` from ethereum/tests commit
`81862e4848585a438d64f911a19b3825f0f4cd95`. An existing sparse checkout can be
reused. Without an override, the runners look under the rocq-of-rust repository's
`tests/revm-testdata/GeneralStateTests`. Do not download or extract the full EEST
archive for this historical target. Local runs default to Cancun; the fork list
may contain Cancun, Prague and Osaka. Builds and fixture runs are sequential.

For a focused case after compiling its dependencies:

```sh
python3 revm/tests/revm_state_fixture_test.py --fork Osaka
```

The current historical selection comprises 141 instruction cases and 270 state
execution cases on each of Cancun and Prague. Osaka selects seven CLZ cases
from EEST `tests-v5.4.0`, retained verbatim under `fixtures/osaka/`, with source
provenance in their `_info` fields and file hashes enforced by the loader.
These selections are not a complete EEST transaction-validation run. They do
not establish native handler correspondence. State checks have explicitly
limited storage/account observations and omit transaction fees, intrinsic gas,
nonce processing and top-level value transfer. The frame runner accepts Osaka and recognizes its full precompile address set;
requests requiring unimplemented cryptographic operations remain incomplete. Unknown or unsupported execution must not be counted as success.

The full-EEST work targets the separately pinned `tests@v20.0.2` corpus. Existing
historical and Osaka smoke results must not be reported as completion of that
corpus. Full transaction, raw-transaction and blockchain coverage requires
additional execution definitions and exact result accounting.

The Cancun KZG point-evaluation precompile has an executable identity-point
slice. It checks the 50,000-gas boundary, 192-byte input, versioned hash and
canonical scalars before handling a commitment and proof that are both the
compressed BLS12-381 point at infinity. In that case the proof succeeds exactly
when the claimed value is zero. All six pinned Cancun direct-call EEST cases
passed through the extracted transaction bridge, including gas and state checks.
Other KZG proofs return incomplete execution; the runner cannot count
them as successful transactions. The focused checks cover the exact pinned
inputs, the precompile output and the unsupported boundary. They do not
establish a general KZG verifier or native correspondence proof.

BLS12-381 precompiles (addresses 11 through 17) implement gas, input-length
and leading-padding rejection following the corresponding Rust modules. G1
addition also checks canonical coordinates and curve membership, then computes
and encodes the sum. As in Rust, addition does not require subgroup membership.
G1 multi-scalar multiplication additionally checks subgroup membership before
skipping zero scalars, reduces scalar values modulo the subgroup order, and
accumulates products in Jacobian coordinates. Validation errors retain the
Rust iterator order, so an earlier invalid point precedes later padding errors.
The provider follows the Arkworks wrapper functions using bounded field and
scalar wrappers with explicit reduction. This is an executable mathematical
model, not a correspondence proof for Arkworks Montgomery representation or
its internal multiplication algorithm. All 91 pinned Osaka G1-addition and
227 G1MSM fixtures pass with authenticated state and hash checks, independently
verified against the pinned selection. The G1MSM selection includes 18 variable
input-length cases. Twelve focused Rocq examples cover addition; eleven cover
MSM scalar boundaries, subgroup rejection and validation order.

P256 (address 256 in Osaka) charges 6,900 gas and returns empty output for input
lengths other than 160 bytes. For 160-byte inputs, its provider checks ECDSA
signature and public-key ranges, curve membership and the P256 verification
equation. Invalid signatures return empty output; valid signatures return a
32-byte word containing one. High-S signatures are accepted. The handwritten
provider follows the P256/ECDSA module boundaries with canonical field/scalar
wrappers and explicit reduction, but does not prove correspondence with
RustCrypto's Montgomery limbs or homogeneous point formulas. BLS requests that
reach unimplemented cryptographic operations still return incomplete execution.
All 397 pinned Osaka EIP-7951 state fixtures pass through the compiled runner,
including authenticated state and hash checks. This covers direct transaction
calls, contract calls and creation, gas boundaries, and valid/invalid signatures.
The native smoke tests also evaluate 35 explicit signature vectors, including
the 17 checked-in Rust vectors. Focused Rocq examples cover input rejection
and representative successful and failed signature verification.
These fixture results do not establish native-provider correspondence. All 64 previously
incomplete Osaka EIP-7702 precompile-pointer cases pass through the compiled
runner with authenticated state and hash checks, including the four that call
G1 addition on two infinity points. This is a focused selection, not completion
of the Osaka corpus.

The go-ethereum-fork integration retains compatibility entry points and its
cross-EVM proof build. Its fixture command delegates to this directory.

Standalone `TransactionAccounting` covers all fourteen state-test forks in
`tests@v20.0.2`: Frontier, Homestead, Tangerine Whistle, Spurious Dragon,
Byzantium, ConstantinopleFix (REVM Petersburg), Istanbul, Berlin, London,
Paris (REVM Merge), Shanghai, Cancun, Prague and Osaka. Its checks track typed
transaction activation, Istanbul calldata pricing, Homestead creation gas,
Shanghai initcode limits and metering, London refunds and beneficiary fees,
Prague calldata floors and the Osaka transaction gas cap. The checked-in Rust
handler validates against a supplied base fee even before London; accounting
preserves that behavior. Its default initcode limit remains 49,152 bytes in
Osaka. These are standalone gas computations with supplied frame outcomes;
execution support still depends on the host, frame and transaction gates.

Transaction pricing and maximum-payment validation use the Rust-named defaults in
`revm_context_interface/simulate/transaction.v::Transaction.Fees`. Its type class
is the getter subset needed for these methods in the current Rust `Transaction`
trait. Gas limits use `u64`, prices use `u128`, and values use `U256`; gas-cost
multiplication and payment additions are checked, while priority and blob-fee
arithmetic saturate as in Rust. Fixture fields are validated before this adapter
is used, and payment errors retain their position after sender-code/nonce checks.
The older linked `Transaction.C/Eq` interface is separate and does not prove
correspondence for these defaults. The executable result module models the payment and environment-validation
errors used here. Other transaction accounting and host fields still use the
existing fixture representation.

Environment validation uses the Rust-named checks in
`revm_handler/simulate/validation.v`: header prerequisites, chain IDs, configured
gas caps, transaction-type activation, fee and blob rules, block gas limits and
initcode size. `Transaction.Fees.C` supplies the shared transaction getters;
typed projection records supply the remaining transaction, block and configuration
fields without claiming correspondence for the older linked context traits.
The reusable validator honors the independent configuration switches and treats
unknown transaction types as Rust's custom type. The fixture adapter retains its
own malformed/unsupported-input boundary and EIP-7702 creation restriction,
including their existing rejection order. Initial/floor gas calculation and
sender-account validation remain separate phases in the adapter.

Transaction settlement now uses `revm_handler/simulate/post_execution.v` for
refund capping, the EIP-7623 floor, caller reimbursement and beneficiary rewards.
The functions follow `post_execution.rs`, with typed context projections passed
explicitly and the concrete journal state passed in and out. Reimbursement uses
saturating `u128` multiplication and a wrapping `U256` additional refund;
beneficiary rewards retain Rust's bounded `u128` arithmetic. Caller credit
precedes beneficiary credit, followed by account cleanup. The account adapter
uses checked balance increases, touches on overflow and zero credit, and records
balance changes only when the balance changes. Its change log remains a concrete
observation log, not Rust's undo journal. The in-memory loader cannot fail; this
is not a native `ContextTr` or `JournalTr` correspondence proof. Output/error
classification and the other transaction phases remain in the fixture adapter.

The regression build also checks legacy, EIP-2930, EIP-1559 and EIP-4844 transactions on
Cancun, Prague and Osaka, including top-level and nested calls and creation,
access-list charges, effective gas prices, maximum-fee affordability, nonce
updates, value transfer, refunds and account cleanup. Blob fees are charged
separately from execution gas and are not refunded or paid to the beneficiary.
The normalized input supplies the blob price and optional transaction blob-count
limit. Header-price derivation and canonical transaction decoding are separate
boundaries; the native handler accepts some inputs that canonical encoding rejects. Top-level ECRECOVER, identity, SHA256,
RIPEMD160 and MODEXP use the same precompile implementations as child calls.
Osaka enforces the 16,777,216 transaction gas cap and retains Prague's calldata
floor. MODEXP selects Osaka pricing and 1,024-byte operand limits for that fork.

EIP-7702 authorization processing uses
`revm_handler/simulate/pre_execution.v::apply_eip7702_auth_list`, following
`pre_execution.rs`. It consumes the `AuthorizationTr` type class from the
matching transaction interface and carries the concrete journal state explicitly.
`journaled_state/simulate/account.v::delegate` calls the separate `set_code` and
`bump_nonce` methods in Rust order. Their arguments use `B256`, `Bytecode` and
`Address`, with explicit journal state passed in and returned.
The typed `revm_state/simulate/account_info.v` setters follow `account_info.rs`:
setting a hash clears cached code, while setting code recalculates its hash.
The journal adapter converts actual fixture accounts to the typed `AccountInfo`
record before calling those setters and preserves storage and transient storage.
`revm_bytecode/simulate/bytecode.v::hash_slow` follows the Rust empty-code branch
and hashes the original byte slice otherwise. This remains an observable-byte
model, not a model or proof of Rust bytecode analysis.
Nonce increments use checked `u64` addition; refund counts and multiplication
use the translated fixed-width operations. Valid Rust scalar inputs and a valid
host are required. The authorization trait has a signed instance in
`transaction/simulate/alloy_types.v`, matching Rust. It uses
`alloy_eip7702/simulate/auth_list.v` for the authorization signing hash and
authority recovery, including parity and low-s checks. Recovery errors are
projected to `None`, as consumed by the Rust trait. The signing input fields
use `U256`, `Address`, `u64` and `u8`; hashing and curve operations reuse the
existing Rocq definitions. Three pinned Osaka authorization signatures and
invalid parity/high-s vectors are checked separately. The three successful
recoveries run in a separate small executable under the native `--smoke` target,
always using standard Zarith extraction to keep signature checks fast; only the cheap rejection checks are
proved by computation during Rocq compilation. Fourteen state checks cover skip ordering, warming, existing-account refunds, repeated
authorities, clearing code and the maximum nonce. Signed type-4 decoding feeds
these definitions before the transaction call checkpoint, so authorization
changes survive a reverted call. Intrinsic gas charges every list entry, while
existing-authority refunds survive revert and halt before the usual cap and
calldata floor. These definitions do not establish correspondence with the native
Rust journal or handler.

`revm_handler/simulate/handler.v::first_frame_input` follows the Rust top-level
one-hop delegation lookup and warming. Nested calls use the existing delegated
account load and charge its cold/warm gas. Both execute in the original call
context; delegating to a precompile does not invoke that precompile. Focused
checks cover these boundaries, delegated senders and skipped authorizations.

The pinned `tests@v20.0.2` Osaka EIP-7702 selection has 747 cases: 683 pass
with authenticated full-state and commitment comparison; 64 remain incomplete
because they call the unimplemented BLS12-381 or P256 precompiles. The five Osaka
CHAINID transaction-type cases and the self-authorization maximum-nonce case
also pass, for 689 passes out of 753 selected state cases. All 124 pinned raw
transaction cases pass validation. These counts do not establish full Osaka
coverage or native REVM correspondence.

Unimplemented precompiles remain explicit unsupported results. Exhausted execution and
transfer-overflow journal behavior not yet modeled return incomplete. Inputs
supply normalized account code hashes; their consistency with code is not
checked by this runner. The historical fixture harness still uses its original
frame entry and does not yet validate the transaction runner's complete output.

Transaction cleanup tracks touched accounts separately from warm accounts and
mutation logs. Calls and creation update that metadata. Rollback restores
ordinary touches but preserves address 3's historical RIPEMD-160 touch exception
after Spurious Dragon. Fee settlement precedes deletion of touched empty
accounts and selfdestructed accounts.

`transaction_fixture.py` normalizes complete state-test inputs for the transaction
runner, preserving sender and beneficiary accounts, signed-envelope fields, fee
caps and selected access lists. It retains expected state/log commitments and
exceptions. Signed requests pass the original envelope to the native bridge,
which invokes Rocq authentication and executes the recovered transaction.
Normalized execution without authentication cannot establish a full fixture pass.

`revm_handler/simulate/transaction_auth.v` supplies standalone executable
`TransactionAuth.authenticate_for_spec`: canonical RLP decoding for signed types
0 through 4, legacy and typed signing payloads, fork-dependent signature checks,
chain-ID matching, secp256k1 recovery and optional declared-sender matching.
Frontier allows high-s signatures; Homestead requires low-s. Protected legacy
signatures activate at Spurious Dragon, and types 1/2/3/4 activate at
Berlin/London/Cancun/Prague using the accounting module's shared activation predicate.
The original `authenticate` API preserves Cancun behavior for existing callers;
the signed JSONL bridge supplies the actual execution fork. Authentication returns
a normalized transaction with its recovered caller. It rejects blob contract
creation in the canonical envelope layer while preserving the normalized
handler's separate semantics. Type-4 contract creation is also rejected by the
canonical decoder. Authorization fields preserve Rust widths, including u8
parity and u64 nonce; in-range invalid signatures are skipped during execution.
Blob network sidecars remain explicitly unsupported. No external cryptographic implementation is substituted
for the Rocq definitions. The decoder and authentication regression modules
check actual historical type 0/1/2/3 envelopes, protected legacy parity, invalid
V/R/S, infinity recovery, malformed RLP and sender mismatches. These computation
checks do not prove decoding, cryptographic correctness or native correspondence.
The JSONL bridge invokes this layer for signed requests and returns explicit
authentication metadata with each result.

Run its parser checks against the existing historical fixture checkout:

```sh
REVM_FIXTURE_ROOT=/path/to/GeneralStateTests python3 revm/tests/transaction_fixture_test.py
```

The concrete simulation can also run as a native OCaml executable. Compile the
extraction and its JSONL bridge from `RocqOfRust`. The builder first refreshes
its canonical production dependencies with sequential make; existing compiled
files alone do not establish that their assumptions are current:

```sh
make -j1 revm/revm_handler/simulate/legacy_call.vo \
  revm/revm_handler/simulate/transaction_auth.vo \
  revm/revm_handler/simulate/ethereum_commitment.vo
python3 revm/tests/native/build.py --smoke --bridge
```

Run these commands with the Rocq and OCaml toolchain active. The bridge also
requires the installed OCaml packages `yojson` and `zarith`; Zarith converts
JSON integers to and from the extracted integer type. Generated Rocq sources,
proof artifacts, OCaml files, binaries and build logs remain in the ignored
`target/revm-native/` directory of the rocq-of-rust checkout. Compilation is
sequential with a default 2 GiB address-space limit and a 64 MiB stack limit.
`--native-memory-limit-mib` changes the cap for OCaml compilation only; the
Osaka CI build uses 8192 MiB because its native library compilation exhausted
the default cap. Rocq compilation, smoke execution and fixture execution retain
their 2 GiB limits. The JSONL
executable is `target/revm-native/native_transaction_bridge`, relative to that
checkout; it reads one signed or normalized request per line and returns the
complete account state, logs, execution status, gas settlement, authentication
metadata and Rocq-computed state/log commitments.

The generator specializes the existing production instruction, frame and
transaction definitions. It compiles equality proofs for those specializations
and projects the static gas schedule from the instruction table. Owned account
loads are specialized with proved producer/consumer equalities. It supplies no
runtime implementations for project axioms and rejects extracted computational
axiom placeholders. Abstract phantom types may remain in the extracted type
signatures. Functional extensionality is used only in erased equality proofs.
The sixteen native smoke checks cover fee settlement, nonce/value updates,
access-list duplicates, blob execution, rollback, rejection ordering, CREATE and
valid/invalid ECRECOVER vectors through the transaction runner.
These checks establish execution of the Rocq simulation and do not establish
correspondence to the native Rust handler or a complete authenticated EEST pass.

The same extracted library exports `TransactionAuth.authenticate_for_spec`,
the compatible modern `TransactionAuth.authenticate`,
`EthereumCommitment.state_root` and `EthereumCommitment.logs_hash` directly from
the canonical simulation modules. Authentication returns its decoded transaction
with the recovered caller, or an explicit rejection/unsupported result. Signed
requests must execute that returned transaction. Commitment functions return
validated state and logs commitments, or `None` for malformed inputs. These
exports add no alternate decoding, recovery or commitment implementation.

`EthereumBlockCommitment` computes transaction and receipt trie roots and
Ethereum logs blooms. Its focused Rocq checks match two pinned Berlin block
headers, including legacy and type-1 receipt roots. `BerlinBlockRlp` decodes
canonical Berlin block headers and transaction envelopes from raw RLP; it does
not execute blocks or validate their state transitions. These definitions are
not yet connected to the native fixture bridge, so blockchain cases remain
explicitly unsupported.

The canonical corpus command reads an existing `tests@v20.0.2` fixture root and
runs signed transactions through the extracted JSONL bridge. It does not download
fixtures or invoke Go tools. From `RocqOfRust`, after building the bridge:

```sh
python3 revm/tests/run_eest_corpus.py --fixtures /path/to/fixtures \
  --results /tmp/revm-eest-all.jsonl --summary /tmp/revm-eest-all-summary.json
python3 revm/tests/verify_eest_corpus.py --fixtures /path/to/fixtures \
  --results /tmp/revm-eest-all.jsonl
```

The default selection inventories all 245,211 indexed cases: 61,813 state tests,
72,715 blockchain tests, 55,275 Engine API tests, 55,275 Engine API X tests,
9 blockchain sync tests and 124 raw transaction tests. Blockchain, Engine API,
sync execution remains explicitly unsupported. State tests and raw transaction
validation use separate requests and result schemas. All 14 pinned state-test
forks can enter execution; remaining semantic gaps are reported explicitly.
Such records make the command return
nonzero. `--format state_test`, `--fork`, exact `--case` IDs and paired
`--shard-index`/`--shard-count` selectors restrict an inventory deliberately;
they do not establish completion of the entire corpus. Independent worker result
files can be supplied together to the verifier. Each output file is created
exclusively so an existing inventory cannot be overwritten.

The loader verifies the immutable metadata SHA256, all six format counts,
the complete state-test fork census, exact fixture IDs, declared fixture hashes,
and SHA256 of canonical fixture payloads excluding `_info`. For state tests the runner sends `execute_signed_transaction` requests. Complete
state fixture passes require Rocq authentication, full state/log commitments and
pinned fixture identity. Raw transaction fixtures send
`validate_signed_transaction` requests and check Rocq validation outcomes.
The verifier requires exactly one record for every selected case and recomputes
comparisons from retained native outputs and the selected fixtures. A recorded
pass flag alone cannot establish a pass. Summaries distinguish selected-case,
complete-state-corpus, complete-raw-transaction-corpus and entire-EEST completion.

Each bridge process has a 2 GiB address-space limit, disables core dumps, and
caps its stderr backing file at 8 MiB. Failure records retain at most 4 KiB of
stderr diagnostics. The verifier bounds each result line before JSON parsing.
The per-case `--timeout` is a wall deadline for bridge input/output; `--fuel`
sets the extracted state-execution budget. Raw validation has structural decoding
bounds and the same wall deadline; its request does not contain execution fuel.
Unsupported, incomplete, mismatched,
timed-out and erroneous cases remain in the flushed result stream and reset
the persistent bridge before the next case. The bridge currently returns one
`Incomplete` result for several unfinished paths; the runner preserves it and
its fuel budget without diagnosing every such result as fuel exhaustion.
`--allow-unpinned` supports development indexes only. It always reports unpinned
results and cannot produce complete pinned fixture or corpus passes. The
synthetic `eest_corpus_test.py` checks transport and accounting without executing
the pinned corpus. Historical fixture results remain a separate limited scope.

The transaction adapter and native bridge recognize all fourteen pinned state-test
fork names. Recognition is separate from execution support: the Rocq transaction
gate still reports unsupported forks explicitly. Pre-London base fee and
pre-Cancun blob fields are disabled; pre-Merge randomness is absent.

The frame and transaction execution gates accept all 14 pinned state-test forks,
from Frontier through Osaka, including Petersburg (ConstantinopleFix). Coinbase
starts warm only from Shanghai. Opening a fork gate does not establish complete
fixture coverage. Precompile account code is bypassed only when that address is
active in the selected fork; before activation, ordinary account code executes.

Expected transaction rejections use an explicit exception-to-handler-error map.
A matching error name alone cannot pass: signed authentication, decoded fields,
unchanged input accounts and the expected state/log commitments are required.
The bridge computes rejection commitments with the same Rocq definitions used
for completed transactions. The signed EEST path applies Geth's maximum sender
nonce rejection through `EestTransaction`; the underlying `LegacyCall` continues
to model native REVM's different behavior at that boundary. Unmapped exceptions
and ambiguous authentication or arithmetic failures remain unsupported, including
canonical blob contract-creation errors. Synthetic comparison checks are not
execution evidence for the corresponding fixtures.

For state-test BLOCKHASH requests, the fixture host computes Geth's
`vmTestBlockHash` value, Keccak-256 of the signed 64-bit block number written
in decimal, when the fixture gives no explicit hash. Other host inputs retain
REVM's external-error behavior for an unavailable block hash.

A type-1 transaction rejected before Berlin is a narrow exception to sender
recovery: the transaction type itself is unavailable, so the Rocq decoder
rejects it before verifying its signature. The comparator labels the exact
`TYPE_1_TX_PRE_FORK` / `TransactionTypeNotSupported [1]` match as
`validated_state_rejection`, with `authentication_verified=false`. It requires
a canonical type-1 envelope consistent with the fixture fields, unchanged
accounts, empty logs, matching Rocq state/log commitments, and the exact
pre-Berlin fork. Only verified pinned identity promotes this result to a corpus
pass. Other authentication failures remain unmapped. Synthetic regression
responses test these guards and are not evidence of native fixture execution.

### Optional Zarith numeric extraction

`native/build.py --numeric-backend zarith --smoke --bridge` keeps the canonical
Rocq definitions and their specialization proofs, but uses the installed
`Stdlib.ExtrOcamlZBigInt` representation for positive, N, and Z. The default is
still inductive extraction; nat stays inductive in both modes. Build the modes
in separate output directories for differential checks. This imports the
standard library's explicitly uncertified arithmetic mappings and trusts the
OCaml/Zarith runtime; it is not a proof of native arithmetic correspondence.
No cryptographic routine or EVM algorithm is replaced by an external provider.

The standard mapping's eager conversion of shift counts to machine integers is
replaced with guarded numeric shifts. Enormous right shifts return the exact
sign extension; enormous zero left shifts remain zero. Nonrepresentable left
shifts of nonzero numbers terminate as resource failures, never a successful
EVM outcome. Bitwise Z operations use Zarith's infinite two's-complement operations.
Division and remainder retain Stdlib's signed and zero-divisor
semantics. Performance is unmeasured until both modes are built and compared.

BLAKE2F (address 9 from Istanbul) executes the Rocq compression definition,
including round-based gas, exact 213-byte input validation and final-flag checks.
Focused primitive and frame tests cover reference vectors and failure ordering.
The eight-million-round reference success vector is not evaluated by local
focused checks; its insufficient-gas case is checked without doing the rounds.

BN254 G1 addition and multiplication at addresses 6 and 7 use executable Rocq
field and Jacobian point arithmetic, with Byzantium/Istanbul gas prices,
zero-padding, coordinate validation and scalar reduction. Focused checks include
35 official Geth vectors and malformed-point/gas boundaries. Address 8 uses an
executable BN254 optimal Ate pairing with strict G2 subgroup validation and
Byzantium/Istanbul gas prices. Focused Rocq checks cover the official Geth
`one_point` false vector, empty and infinity inputs, malformed lengths, gas
boundaries, and child-call dispatch. All fourteen official Geth pairing vectors
passed through the extracted bridge with matching output and gas. These
definitions do not claim
native-provider correspondence or a cryptographic correctness proof.

The fixture adapter supplies Osaka's six-blob transaction cap independently of
`blobSchedule.max`, which describes the block schedule. Blob-price calculation
still uses the supplied schedule. EEST floor-gas and transaction-gas-cap exception
mappings check the applicable fork and exact handler details; floor-gas rejection
also checks that the initial intrinsic gas cost did not already exceed the limit.

### Resumable Osaka inventory

The manual **REVM Osaka inventory** workflow targets exactly 14,614 Osaka state
cases and 56 Osaka raw transaction cases from the pinned `tests@v20.0.2` index.
Blocks, Engine API and sync cases are outside this selection. It builds one native
bridge and uses 16 deterministic shards with at most two jobs running together.
The `osaka-verified-inventory` artifact contains summaries and a diagnostic
`failure-groups.json`, grouping nonpassing cases by status and test function with
representative IDs. These groups do not establish a shared root cause.
The workflow reports failure while any selected case is missing or does not pass;
a complete inventory is not the same as complete semantic coverage.

The workflow must exist on the default branch before GitHub enables manual
execution. Relevant pull requests run the lightweight Python checks only. After
merging, start it from Actions, **REVM Osaka inventory**, **Run workflow**. To
continue interrupted jobs, use **Re-run failed jobs** on the same run. This keeps
the successful preparation artifact and restores each failed shard's result files
and manifests. Starting a new workflow run builds a new inventory instead. Results
and the executable/fixture bundle are retained for 14 days; missing preparation
artifacts require a new run. Hard cancellation or runner loss can prevent the
latest checkpoint from uploading, so CI recovery is limited to uploaded evidence.

Local runs can use the existing `run_eest_corpus.py` command with `--resume` and
the same `--results` path. Keep its `.manifest.json` sidecar alongside the JSONL
file, in a persistent directory rather than `/tmp`. The manifest binds the exact
selection, fixture pin, executable digest, Python harness digest, fuel and timeout.
Completed records are independently checked before they are skipped. Each new
record is synchronized to disk. A partial final line is discarded and retried;
malformed complete records and changed execution settings are rejected. A second
writer cannot append to the same checkpoint concurrently. Previously completed
nonpassing cases are also retained; `--resume` continues interrupted work, not
semantic retries. After changing the executable or harness, use a new result path.

The verifier accepts multiple shard files and rejects mixed execution identities.
Supply `--bridge /path/to/native_transaction_bridge` to require results from that
exact executable. Old result files remain verifiable, but lack the manifest needed
for resumption. Their results cannot be mixed with newly identified records.

`native/build.py --reuse --numeric-backend zarith --smoke --bridge` can reuse a
successful local build when its source/toolchain/options fingerprint and output
hashes match. The first such invocation needs a successful build to establish its
stamp. Requested smoke executables still run on a cache hit. The default behavior
and `--no-cache` rebuild; interrupted builds do not publish a success stamp. Reuse
assumes installed dependency libraries are unchanged when their package versions
are unchanged. It is a local optimization, not a portable build certificate.

### Raw transaction validation protocol

`transaction_format.py` reads the indexed fixture's exact `txbytes` and single
`result` fork. It sends only protocol, request, fork, chain ID 1 and raw bytes;
expected exceptions, sender, hash and intrinsic gas remain outside Rocq. The
request name is `validate_signed_transaction`. Responses carry protocol 1,
engine `rocq_revm` and scope `raw_transaction`. `Valid` supplies an integer
sender, a 32-byte transaction hash and integer `intrinsic_gas`. `Rejected` and
`Unsupported` supply a nonempty reason and an unsigned integer details array.
`Incomplete` supplies no additional fields. No state-execution result can be
accepted through this raw-validation parser.

The fixture's positive result requires exact sender, hash and intrinsic-gas
agreement. Its negative result requires a definite Rocq `Rejected` result,
matching the transaction-test utility's validity check. Exception strings are
diagnostic alternatives, so this scope does not establish equality of client
error messages. Unsupported types, unavailable authentication and incomplete
computation remain nonpasses even when the fixture expects an exception. A
bridge must serialize only the canonical Rocq rejection enum as `Rejected`;
process failures and missing semantics must not be converted into rejections.
Only independently verified pinned identity promotes a matched result to a
corpus pass. `full_transaction_corpus_pass` additionally requires all 124 exact
raw-transaction identities to pass; it does not establish entire-EEST completion.

The retained tests@v20.0.2 raw corpus has 14 nonce-overflow cases, two empty
EIP-7702 authorization-list cases, 92 authorization-format cases and 16 cases
with authorization-signature exception alternatives. Those 16 encode
oversized parity (`2^8`) or signature scalars (`2^256`), which are fixed-width
encoding failures. In-range invalid authorization signatures have different
semantics and must not be rejected merely because recovery fails. Parser and
synthetic response tests do not establish execution of these pinned fixtures.

For an archive-sized run with bounded disk use, stream the pinned compressed
archive through `run_eest_stream.py`. This entry point uses only the Python
standard library and the canonical runner/verifier. It accepts a local archive,
or `--archive -` for a compressed stream on stdin; it does not download fixtures.
From `RocqOfRust`:

```sh
python3 revm/tests/run_eest_stream.py --index /path/to/fixtures/.meta/index.json \
  --archive /path/to/fixtures.tar.gz --work /tmp/revm-eest-stream
```

The index is parsed one bounded item at a time into a disk-backed SQLite
inventory. Its exact digest, all 245,211 identities and six-format/fork census
are checked before publication. The actual pinned index took 29 MiB peak RSS
and 179 MiB of SQLite storage in the staging benchmark. This entry point executes
state and raw transaction cases and records the other four formats explicitly
as unsupported. Unsupported records claim index identity only; their payloads
are not separately compared. The final archive checksum binds the entire input
to the pinned release. The command returns nonzero while any format remains
unsupported.

One executable fixture member is materialized at a time. For every case, the
existing independent verifier parses the retained native result, regenerates the
signed request, and recomputes the fixture comparison while the member exists.
Successful outputs are replaced by compact receipts carrying request, native
output, full-record and semantic-record hashes. Each nonpassing executable case
retains its full record and the shared fixture member as zlib-compressed evidence.
The receipt chain, records and checkpoint updates are atomic SQLite transactions;
evidence files are synchronized before their receipts are committed.

`--member-bytes` defaults to 128 MiB and `--evidence-bytes` to 512 MiB. Exceeding
a member bound or the retained-evidence budget stops the run incomplete, leaving
uncommitted cases pending. The disk bound additionally includes the inventory,
compact receipts, one temporary member, and compression scratch space. No full
uncompressed archive or collection of successful state outputs is retained.
The existing per-process 2 GiB memory limit and per-case wall/fuel limits apply.
Archive progress is printed to stderr at approximately 30-second intervals.

Resume with the same command and `--resume`. The index identities, bridge hash,
harness hashes and execution limits must match; storage budgets may only increase.
Resume reads the archive again from its beginning and skips durable checked cases.
Interrupted temporary members and compression scratch files are removed under the
work-directory lock. Missing members, duplicate selected members, malformed paths,
truncated gzip streams and a wrong full compressed SHA256 all prevent completion.
Even a resumed run must read the entire archive and check its exact SHA256 before
any complete-corpus flag can become true. A complete accounting inventory may
still contain unsupported cases and cannot establish a full-EEST pass.

Compact receipts are local attestations that live comparison ran. Hash checking
alone cannot independently verify discarded native semantics, and the summary
states this explicitly. Add `--resume --replay` to execute every retained executable
case again, perform fresh live comparison, and check its semantic/request/native
hashes against the receipts. Replay requires the archive and identified bridge;
it does not infer native correctness from hashes. The synthetic
`eest_stream_test.py` exercises streaming, accounting, corruption, resume, evidence
budgets and actual mock-process replay without claiming pinned fixture execution.
