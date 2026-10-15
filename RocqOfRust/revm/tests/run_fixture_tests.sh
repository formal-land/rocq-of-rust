#!/usr/bin/env bash

set -euo pipefail

rocq_of_rust="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"

fixture_fork_list="${REVM_TEST_FORKS-Cancun}"
read -r -a fixture_forks <<< "${fixture_fork_list//$'\n'/ }"
if (( ${#fixture_forks[@]} == 0 )); then
  echo "REVM_TEST_FORKS must contain Cancun, Prague, or Osaka" >&2
  exit 1
fi
for fork in "${fixture_forks[@]}"; do
  case "$fork" in
    Cancun|Prague|Osaka) ;;
    *) echo "unsupported REVM fixture fork: $fork" >&2; exit 1 ;;
  esac
done

targets=(
  revm/revm_interpreter/tests/gas_refunds.vo
  revm/revm_context_interface/tests/transaction_fees.vo
  alloy_eip7702/tests/auth_list.vo
  revm/revm_precompile/tests/blake2.vo
  revm/revm_precompile/tests/bn254.vo
  revm/revm_precompile/tests/bn254_pairing.vo
  revm/revm_precompile/tests/bn254_pairing_run.vo
  revm/revm_precompile/tests/kzg_point_evaluation.vo
  revm/revm_precompile/tests/secp256k1.vo
  revm/revm_context_interface/journaled_state/tests/account.vo
  revm/revm_handler/tests/pre_execution.vo
  revm/revm_handler/tests/handler.vo
  revm/revm_handler/tests/authorization_call.vo
  revm/revm_interpreter/tests/delegated_calls.vo
  revm/revm_handler/tests/legacy_call.vo
  revm/revm_handler/tests/eest_transaction.vo
  revm/revm_handler/tests/legacy_create.vo
  revm/revm_handler/tests/historical_frames.vo
  revm/revm_handler/tests/earliest_forks.vo
  revm/revm_handler/tests/transaction_accounting.vo
  revm/revm_handler/tests/post_execution.vo
  revm/revm_handler/tests/transaction_validation.vo
  revm/revm_handler/tests/ethereum_rlp.vo
  revm/revm_handler/tests/ethereum_rlp_decode.vo
  revm/revm_handler/tests/ethereum_commitment.vo
  revm/revm_handler/tests/ethereum_block_commitment.vo
  revm/revm_handler/simulate/blockchain_berlin.vo
  revm/revm_handler/tests/transaction_auth.vo
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
  revm/revm_interpreter/tests/account_access.vo
  revm/revm_interpreter/tests/call_gas.vo
  revm/revm_interpreter/tests/call_accounts.vo
  revm/revm_interpreter/tests/calls.vo
  revm/revm_interpreter/tests/call_context.vo
  revm/revm_interpreter/tests/code_hash.vo
  revm/revm_interpreter/tests/create_address.vo
  revm/revm_interpreter/tests/create_frame.vo
  revm/revm_interpreter/tests/create.vo
  revm/revm_interpreter/tests/external_code.vo
  revm/revm_interpreter/tests/event_logs.vo
  revm/revm_interpreter/tests/log_observation.vo
  revm/revm_interpreter/tests/frame_output.vo
  revm/revm_interpreter/tests/frame.vo
  revm/revm_interpreter/tests/frame_rollback.vo
  revm/revm_interpreter/tests/interpreter.vo
  revm/revm_interpreter/tests/memory_copy.vo
  revm/revm_interpreter/tests/mcopy.vo
  revm/revm_interpreter/tests/environment_opcodes.vo
  revm/revm_interpreter/tests/sstore_refund.vo
  revm/revm_interpreter/tests/stateful_dispatch.vo
  revm/revm_interpreter/tests/static_calls.vo
  revm/revm_interpreter/tests/selfdestruct.vo
  revm/revm_interpreter/tests/identity_precompile.vo
  revm/revm_interpreter/tests/blake2_precompile.vo
  revm/revm_interpreter/tests/bn254_precompile.vo
  revm/revm_interpreter/tests/bn254_pairing_precompile.vo
  revm/revm_interpreter/tests/ecrecover_precompile.vo
  revm/revm_interpreter/tests/sha256_precompile.vo
  revm/revm_interpreter/tests/ripemd160_precompile.vo
  revm/revm_interpreter/tests/modexp_precompile.vo
  revm/revm_interpreter/tests/transient_storage.vo
  revm/revm_interpreter/tests/keccak.vo
)

if [[ -v REVM_FIXTURE_ROOT ]]; then
  REVM_FIXTURE_ROOT="$(python3 -c 'import pathlib, sys; print(pathlib.Path(sys.argv[1]).expanduser().resolve())' "$REVM_FIXTURE_ROOT")"
  export REVM_FIXTURE_ROOT
fi
cd "$rocq_of_rust"
python3 -m unittest \
  revm/tests/revm_fixture_test_test.py \
  revm/tests/revm_state_fixture_test_test.py
python3 revm/tests/transaction_fixture_test.py
python3 revm/tests/transaction_compare_test.py
python3 revm/tests/eest_corpus_test.py
make -C "$rocq_of_rust" "${targets[@]}"
for fork in "${fixture_forks[@]}"; do
  echo "Checking Rocq REVM reference fixtures for $fork"
  if [[ "$fork" != Osaka ]]; then
    python3 revm/tests/revm_fixture_test.py --fork "$fork"
  fi
  python3 revm/tests/revm_state_fixture_test.py --fork "$fork"
done
