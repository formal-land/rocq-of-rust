#!/usr/bin/env bash

set -euo pipefail

rocq_of_rust="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"

targets=(
  revm/revm_state/tests/account.vo
  revm/revm_context_interface/journaled_state/tests/account_state.vo
  revm/revm_context/tests/journal.vo
  revm/revm_context/tests/journal_load.vo
  revm/revm_context/tests/context.vo
  revm/revm_context/tests/interpreter.vo
  revm/revm_interpreter/tests/runtime.vo
  revm/revm_handler/tests/typed_frames.vo
  revm/revm_handler/tests/typed_pre_execution.vo
  revm/revm_handler/tests/typed_handler.vo
  revm/revm_handler/tests/typed_precompiles.vo
  revm/revm_handler/tests/eest_context.vo
  revm/revm_interpreter/tests/gas_refunds.vo
  revm/revm_context_interface/tests/transaction_fees.vo
  alloy_eip7702/tests/auth_list.vo
  revm/revm_interpreter/tests/precompile_boundaries.vo
  revm/revm_precompile/tests/bls12_381.vo
  revm/revm_precompile/tests/bls12_381_g1.vo
  revm/revm_precompile/tests/bls12_381_g1_msm.vo
  revm/revm_precompile/tests/bls12_381_g2.vo
  revm/revm_precompile/tests/bls12_381_map.vo
  revm/revm_precompile/tests/bls12_381_pairing.vo
  revm/revm_precompile/tests/secp256r1.vo
  revm/revm_precompile/tests/secp256r1_verification.vo
  revm/revm_precompile/tests/blake2.vo
  revm/revm_precompile/tests/bn254.vo
  revm/revm_precompile/tests/bn254_pairing.vo
  revm/revm_precompile/tests/bn254_pairing_run.vo
  revm/revm_precompile/tests/kzg_arkworks.vo
  revm/revm_precompile/tests/kzg_point_evaluation.vo
  revm/revm_precompile/tests/secp256k1.vo
  revm/revm_handler/tests/eest_transaction.vo
  revm/revm_handler/tests/transaction_accounting.vo
  revm/revm_handler/tests/validation.vo
  revm/revm_handler/tests/transaction_validation.vo
  revm/revm_handler/tests/ethereum_rlp.vo
  revm/revm_handler/tests/ethereum_rlp_decode.vo
  revm/revm_handler/tests/ethereum_commitment.vo
  revm/revm_handler/tests/ethereum_block_commitment.vo
  revm/revm_interpreter/instructions/simulate/arithmetic/add.vo
  revm/revm_interpreter/instructions/simulate/arithmetic/addmod.vo
  revm/revm_interpreter/instructions/simulate/arithmetic/div.vo
  revm/revm_interpreter/instructions/simulate/arithmetic/exp.vo
  revm/revm_interpreter/instructions/simulate/arithmetic/mul.vo
  revm/revm_interpreter/instructions/simulate/arithmetic/mulmod.vo
  revm/revm_interpreter/instructions/simulate/arithmetic/rem.vo
  revm/revm_interpreter/instructions/simulate/arithmetic/sdiv.vo
  revm/revm_interpreter/instructions/simulate/arithmetic/signextend.vo
  revm/revm_interpreter/instructions/simulate/arithmetic/smod.vo
  revm/revm_interpreter/instructions/simulate/arithmetic/sub.vo
  revm/revm_interpreter/instructions/tests/contract.vo
  revm/revm_interpreter/instructions/tests/memory.vo
  revm/revm_interpreter/tests/dispatch.vo
  revm/revm_interpreter/tests/call_gas.vo
  revm/revm_interpreter/tests/create_address.vo
  revm/revm_interpreter/tests/frame_output.vo
  revm/revm_interpreter/tests/interpreter.vo
  revm/revm_interpreter/tests/memory_copy.vo
  revm/revm_interpreter/tests/mcopy.vo
)

if [[ -v REVM_FIXTURE_ROOT ]]; then
  REVM_FIXTURE_ROOT="$(python3 -c 'import pathlib, sys; print(pathlib.Path(sys.argv[1]).expanduser().resolve())' "$REVM_FIXTURE_ROOT")"
  export REVM_FIXTURE_ROOT
fi
cd "$rocq_of_rust"
# This test checks both compiler caps and must precede the shell's hard limit.
python3 revm/tests/native/test_build_reuse.py
ulimit -v 2097152
python3 revm/tests/eest_corpus_test.py
python3 revm/tests/eest_resume_test.py
python3 revm/tests/acquire_osaka_fixtures_test.py
python3 revm/tests/summarize_eest_failures_test.py
make -j1 -C "$rocq_of_rust" "${targets[@]}"
# This historical instruction harness is independent of the Osaka executor.
# It is optional because it needs a separate ethereum/tests snapshot.
if [[ -v REVM_FIXTURE_ROOT ]]; then
  python3 revm/tests/transaction_fixture_test.py
  python3 revm/tests/transaction_compare_test.py
  python3 -m unittest revm/tests/revm_fixture_test_test.py
  python3 revm/tests/revm_fixture_test.py --fork Cancun
fi

# These unchanged signature vm_compute examples can exceed an hour.
# Osaka raw-transaction EEST and native authentication checks remain mandatory.
if [[ "${REVM_SLOW_TESTS-0}" == 1 ]]; then
  timeout 3600 make -j1 revm/revm_handler/tests/transaction_auth.vo
fi
