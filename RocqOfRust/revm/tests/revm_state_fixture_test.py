#!/usr/bin/env python3
"""Run a fixture-derived stateful program against the Rocq REVM dispatcher."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import subprocess
import sys
import tempfile
from dataclasses import dataclass, replace
from pathlib import Path
from typing import Any

from Crypto.Hash import keccak


ROCQ_ROOT = Path(__file__).resolve().parents[2]
REPO_ROOT = ROCQ_ROOT.parent
FIXTURE_ROOT = Path(os.environ.get(
    "REVM_FIXTURE_ROOT", REPO_ROOT / "tests/revm-testdata/GeneralStateTests"
)).expanduser().resolve()
OSAKA_FIXTURE_ROOT = Path(__file__).resolve().parent / "fixtures/osaka"
OSAKA_GAS_FIXTURE = OSAKA_FIXTURE_ROOT / "test_clz_gas_cost.json"
OSAKA_MEMORY_FIXTURE = OSAKA_FIXTURE_ROOT / "test_clz_with_memory_operation.json"
# Unmodified EEST snapshots with explicit Osaka post-states; never reuse Prague
# expectations for Osaka. Values pin the original bytes and named-test counts.
OSAKA_SELECTION = {
    OSAKA_GAS_FIXTURE: ("4e67a43059dedce6c09afdfbd71b89a37370b44182acf2c53333b744c5acacf2", 1),
    OSAKA_MEMORY_FIXTURE: ("a3a02910fa5895394d050a84b1dcfed2c5d4dce0f0923e48ce99b3b1cabc17e6", 6),
}
OSAKA_FIXTURES = tuple(OSAKA_SELECTION)
ADD11_FIXTURE = (
    FIXTURE_ROOT / "stExample/add11.json"
)
ACCESS_LIST_FIXTURE = (
    FIXTURE_ROOT / "stExample/accessListExample.json"
)
SHIFT_FIXTURE_ROOT = FIXTURE_ROOT / "stShift"
CHAIN_ID_FIXTURE_ROOT = FIXTURE_ROOT / "stChainId"
SLOAD_FIXTURE_ROOT = FIXTURE_ROOT / "stSLoadTest"
SELF_BALANCE_FIXTURE_ROOT = (
    FIXTURE_ROOT / "stSelfBalance"
)
SELF_BALANCE_FIXTURES = tuple(
    SELF_BALANCE_FIXTURE_ROOT / name
    for name in (
        "selfBalance.json",
        "selfBalanceGasCost.json",
        "selfBalanceEqualsBalance.json",
    )
)
SSTORE_GAS_FIXTURE = (
    FIXTURE_ROOT / "stSStoreTest/sstoreGas.json"
)
BALANCE_GAS_FIXTURE = (
    FIXTURE_ROOT / "stEIP150singleCodeGasPrices/RawBalanceGas.json"
)
MEMORY_FIXTURE_ROOT = FIXTURE_ROOT / "stMemoryTest"
MEMORY_RETURN_FIXTURE = MEMORY_FIXTURE_ROOT / "memReturn.json"
MCOPY_FIXTURE = FIXTURE_ROOT / "Cancun/stEIP5656-MCOPY/MCOPY.json"
MEMORY_FIXTURES = tuple(
    MEMORY_FIXTURE_ROOT / name
    for name in (
        "mload8bitBound.json",
        "mload16bitBound.json",
        "mem0b_singleByte.json",
        "mem31b_singleByte.json",
        "mem32b_singleByte.json",
        "mem33b_singleByte.json",
        "calldatacopy_dejavu.json",
        "calldatacopy_dejavu2.json",
        "codecopy_dejavu.json",
        "codecopy_dejavu2.json",
    )
)
# Direct programs with nonempty calldata, 50,000-byte copies, and storage
# observations of copied bytes. They do not execute nested calls.
CALLDATA_COPY_FIXTURES = tuple(
    FIXTURE_ROOT / family / name
    for family, name in (
        ("stRandom", "randomStatetest217.json"),
        ("stRandom", "randomStatetest301.json"),
        ("stRandom2", "randomStatetest586.json"),
    )
)
EXTERNAL_CODE_FIXTURES = tuple(
    FIXTURE_ROOT / family / name
    for family, name in (
        ("stEIP150singleCodeGasPrices", "RawExtCodeSizeGas.json"),
        ("stEIP150singleCodeGasPrices", "RawExtCodeCopyGas.json"),
        ("stEIP150singleCodeGasPrices", "RawExtCodeCopyMemoryGas.json"),
        ("stEIP158Specific", "EXTCODESIZE_toEpmtyParis.json"),
        ("stEIP158Specific", "EXTCODESIZE_toNonExistent.json"),
        ("stExtCodeHash", "extCodeCopyBounds.json"),
        ("stMemoryTest", "extcodecopy_dejavu.json"),
    )
)
CALL_INPUT_FIXTURES = (
    FIXTURE_ROOT / "stSystemOperationsTest/callValue.json",
    FIXTURE_ROOT / "stSystemOperationsTest/TestNameRegistrator.json",
)
RETURN_DATA_FIXTURE_ROOT = (
    FIXTURE_ROOT / "stReturnDataTest"
)
CREATE2_FIXTURE_ROOT = FIXTURE_ROOT / "stCreate2"
CONSTRUCTOR_CONTEXT_FIXTURES = tuple(
    FIXTURE_ROOT / family / name
    for family, name in (
        ("stCreateTest", "CodeInConstructor.json"),
        ("stCreateTest", "CreateCollisionResults.json"),
        ("stCreateTest", "CREATE_HighNonce.json"),
        ("stCreateTest", "CREATE_HighNonceMinus1.json"),
        ("stExtCodeHash", "createEmptyThenExtcodehash.json"),
    )
)
CREATE_FIXTURES = tuple(
    RETURN_DATA_FIXTURE_ROOT / name
    for name in (
        "returndatasize_following_successful_create.json",
        "returndatacopy_0_0_following_successful_create.json",
        "returndatacopy_following_create.json",
        "returndatacopy_following_successful_create.json",
        "returndatacopy_afterFailing_create.json",
        "returndatacopy_following_revert_in_create.json",
        "call_then_create_successful_then_returndatasize.json",
        "call_outsize_then_create_successful_then_returndatasize.json",
    )
) + tuple(
    CREATE2_FIXTURE_ROOT / name
    for name in (
        "returndatasize_following_successful_create.json",
        "returndatacopy_0_0_following_successful_create.json",
        "returndatacopy_following_successful_create.json",
        "returndatacopy_afterFailing_create.json",
        "returndatacopy_following_revert_in_create.json",
        "call_then_create2_successful_then_returndatasize.json",
        "call_outsize_then_create2_successful_then_returndatasize.json",
    )
)
CREATE_FIXTURES += CONSTRUCTOR_CONTEXT_FIXTURES
SELFDESTRUCT_DIRECT_FIXTURES = tuple(
    FIXTURE_ROOT / "stZeroCallsTest" / name
    for name in (
        "ZeroValue_SUICIDE.json",
        "ZeroValue_SUICIDE_ToEmpty_Paris.json",
        "ZeroValue_SUICIDE_ToNonZeroBalance.json",
        "ZeroValue_SUICIDE_ToOneStorageKey_Paris.json",
    )
)
SELFDESTRUCT_CALL_FIXTURE = (
    FIXTURE_ROOT / "VMTests/vmTests/suicide.json"
)
SELFDESTRUCT_FIXTURES = SELFDESTRUCT_DIRECT_FIXTURES + (SELFDESTRUCT_CALL_FIXTURE,)
IDENTITY_ACCOUNT_FIXTURES = tuple(
    FIXTURE_ROOT / directory / name
    for directory, name in (
        ("stPreCompiledContracts", "identity_to_bigger.json"),
        ("stPreCompiledContracts", "identity_to_smaller.json"),
        ("stReturnDataTest", "create_callprecompile_returndatasize.json"),
    )
)
# These fixed, zero-call-value programs do not observe the unapplied transaction
# entry transfer. Python tests lock their code, gas, input and storage observations.
IDENTITY_STORAGE_FIXTURES = tuple(
    FIXTURE_ROOT / directory / name
    for directory, name in (
        ("stPreCompiledContracts2", "CallIdentitiy_1.json"),
        ("stPreCompiledContracts2", "CallIdentity_2.json"),
        ("stPreCompiledContracts2", "CallIdentity_6_inputShorterThanOutput.json"),
        ("stPreCompiledContracts2", "CallIdentity_4_gas17.json"),
        ("stPreCompiledContracts2", "CallIdentity_4_gas18.json"),
        ("stPreCompiledContracts2", "CALLCODEIdentity_4_gas17.json"),
        ("stPreCompiledContracts2", "CALLCODEIdentity_4_gas18.json"),
        ("stStaticCall", "static_CallIdentity_4_gas17.json"),
        ("stStaticCall", "static_CallIdentity_4_gas18.json"),
    )
)
IDENTITY_FIXTURES = IDENTITY_ACCOUNT_FIXTURES + IDENTITY_STORAGE_FIXTURES
# Like the identity storage selection, these fixed zero-value calls cannot observe
# the omitted transaction entry transfer. Tests lock the complete programs.
SHA256_FIXTURES = tuple(
    FIXTURE_ROOT / directory / f"{prefix}Sha256{suffix}.json"
    for directory, prefix in (
        ("stPreCompiledContracts2", "Call"),
        ("stPreCompiledContracts2", "CALLCODE"),
        ("stStaticCall", "static_Call"),
    )
    for suffix in ("_1", "_2", "_3_postfix0", "_4_gas99")
)
# RIPEMD160 uses the same bounded, entry-transfer-independent storage oracle.
RIPEMD160_FIXTURES = tuple(
    FIXTURE_ROOT / directory / f"{prefix}Ripemd160{suffix}.json"
    for directory, prefix in (
        ("stPreCompiledContracts2", "Call"),
        ("stPreCompiledContracts2", "CALLCODE"),
        ("stStaticCall", "static_Call"),
    )
    for suffix in ("_1", "_2", "_3_postfixed0", "_4_gas719")
)
# Pin selected post cases before parsing their advertised lengths. Unselected
# cases include enormous operands and must not enter the default batch.
MODEXP_SELECTION = {
    FIXTURE_ROOT / "stPreCompiledContracts/modexp.json": (
        "4b477590a1f5e6ad0a662a672e432978be9d84b13d82b777f1d9a0545e8c5e3c",
        (1, 33, 117, 37, 133, 141, 69, 73),
    ),
    FIXTURE_ROOT / "stReturnDataTest/modexp_modsize0_returndatasize.json": (
        "ef12791cd182057220f26db6235d8bde845a724d67bbf99466819ff19fd4f142",
        (0, 1, 2, 3),
    ),
}
MODEXP_FIXTURES = tuple(MODEXP_SELECTION)
ACCOUNT_STATE_FIXTURES = CREATE_FIXTURES + SELFDESTRUCT_FIXTURES + IDENTITY_ACCOUNT_FIXTURES
RETURN_DATA_FIXTURES = tuple(
    RETURN_DATA_FIXTURE_ROOT / name
    for name in (
        "returndatasize_initial.json",
        "returndatasize_initial_zero_read.json",
        "returndatacopy_initial.json",
        "returndatacopy_initial_256.json",
        "returndatacopy_initial_big_sum.json",
    )
)
# These programs deliberately read past an empty return buffer. Storage alone
# cannot distinguish the expected exceptional halt from successful execution.
RETURN_DATA_FAILURE_FIXTURES = frozenset((
    *RETURN_DATA_FIXTURES[2:],
    RETURN_DATA_FIXTURE_ROOT / "returndatacopy_after_failing_callcode.json",
    RETURN_DATA_FIXTURE_ROOT / "returndatacopy_after_failing_staticcall.json",
    RETURN_DATA_FIXTURE_ROOT / "returndatacopy_following_create.json",
    RETURN_DATA_FIXTURE_ROOT / "returndatacopy_following_successful_create.json",
    CREATE2_FIXTURE_ROOT / "returndatacopy_following_successful_create.json",
))
CALL_CONTEXT_FIXTURES = tuple(
    FIXTURE_ROOT / family / name
    for family, name in (
        ("stReturnDataTest", "returndatasize_after_successful_callcode.json"),
        ("stReturnDataTest", "returndatacopy_after_successful_callcode.json"),
        ("stReturnDataTest", "returndatasize_after_failing_callcode.json"),
        ("stReturnDataTest", "returndatacopy_after_failing_callcode.json"),
        ("stReturnDataTest", "returndatasize_after_successful_delegatecall.json"),
        ("stReturnDataTest", "returndatacopy_after_successful_delegatecall.json"),
        ("stReturnDataTest", "returndatasize_after_failing_delegatecall.json"),
        ("stDelegatecallTestHomestead", "delegatecallBasic.json"),
        ("stDelegatecallTestHomestead", "delegatecallSenderCheck.json"),
        ("stDelegatecallTestHomestead", "delegatecallEmptycontract.json"),
    )
)
STATIC_RETURN_FIXTURE = FIXTURE_ROOT / "stStaticCall/static_ReturnTest.json"
STATIC_CALL_FIXTURES = tuple(
    RETURN_DATA_FIXTURE_ROOT / name
    for name in (
        "returndatasize_after_successful_staticcall.json",
        "returndatasize_after_failing_staticcall.json",
        "returndatacopy_after_successful_staticcall.json",
        "returndatacopy_after_failing_staticcall.json",
        "returndatacopy_after_revert_in_staticcall.json",
    )
) + (STATIC_RETURN_FIXTURE,)
TRANSIENT_STORAGE_FIXTURES = tuple(
    FIXTURE_ROOT / "Cancun/stEIP1153-transientStorage" / name
    for name in (
        "10_revertUndoesStoreAfterReturn.json",
        "14_revertAfterNestedStaticcall.json",
        "17_tstoreGas.json",
        "19_oogUndoesTransientStore.json",
    )
)
# The failing-delegatecall copy file sends the transaction to an account with
# no code, so its unchanged storage does not exercise DELEGATECALL.
CALL_EXECUTION_FIXTURES = tuple(
    RETURN_DATA_FIXTURE_ROOT / name
    for name in (
        "returndatacopy_following_call.json",
        "returndatacopy_following_revert.json",
        "call_then_call_value_fail_then_returndatasize.json",
    )
) + CALL_CONTEXT_FIXTURES + STATIC_CALL_FIXTURES + TRANSIENT_STORAGE_FIXTURES + CREATE_FIXTURES
# These direct programs exhaust gas while expanding memory, before any write.
MEMORY_COPY_FAILURE_FIXTURES = frozenset(
    MEMORY_FIXTURE_ROOT / name
    for name in ("calldatacopy_dejavu.json", "codecopy_dejavu.json", "extcodecopy_dejavu.json")
)
EXECUTION_FUEL = 100_000
LOG_FIXTURE_ROOT = FIXTURE_ROOT / "stLogTests"
LOG_FIXTURES = tuple(sorted(LOG_FIXTURE_ROOT.glob("*.json")))
CALL_EXECUTION_FIXTURES += LOG_FIXTURES
CALL_EXECUTION_FIXTURES += SELFDESTRUCT_FIXTURES + IDENTITY_FIXTURES + SHA256_FIXTURES + RIPEMD160_FIXTURES + MODEXP_FIXTURES
REVERT_FIXTURE = FIXTURE_ROOT / "stRevertTest/RevertOpcode.json"
REVERT_UNDERFLOW_FIXTURE = (
    FIXTURE_ROOT / "stRevertTest/RevertOnEmptyStack.json"
)
CODE_HASH_FIXTURES = tuple(
    FIXTURE_ROOT / "stExtCodeHash" / name
    for name in (
        "extCodeHashSelf.json",
        "extCodeHashDynamicArgument.json",
        "extCodeHashPrecompiles.json",
    )
)
DEFAULT_FIXTURES = (
    ADD11_FIXTURE,
    ACCESS_LIST_FIXTURE,
    *sorted(SHIFT_FIXTURE_ROOT.glob("*.json")),
    *sorted(CHAIN_ID_FIXTURE_ROOT.glob("*.json")),
    *sorted(SLOAD_FIXTURE_ROOT.glob("*.json")),
    *SELF_BALANCE_FIXTURES,
    SSTORE_GAS_FIXTURE,
    BALANCE_GAS_FIXTURE,
    *MEMORY_FIXTURES,
    MCOPY_FIXTURE,
    *CALLDATA_COPY_FIXTURES,
    *EXTERNAL_CODE_FIXTURES,
    *CODE_HASH_FIXTURES,
    *CALL_INPUT_FIXTURES,
    *RETURN_DATA_FIXTURES,
    *CALL_EXECUTION_FIXTURES,
    MEMORY_RETURN_FIXTURE,
    REVERT_FIXTURE,
    REVERT_UNDERFLOW_FIXTURE,
)
# Retain the singular name for callers that select the original smoke test.
DEFAULT_FIXTURE = ADD11_FIXTURE


class FixtureError(RuntimeError):
    pass


@dataclass(frozen=True)
class Account:
    address: int
    balance: int
    nonce: int
    code: tuple[int, ...]
    storage: tuple[tuple[int, int], ...]


@dataclass(frozen=True)
class StateCase:
    name: str
    fork: str
    spec_id: str
    target_address: int
    caller_address: int
    chain_id: int
    gas_price: int
    transaction_gas_limit: int
    transaction_nonce: int
    call_value: int
    calldata: tuple[int, ...]
    coinbase: int
    gas_limit: int
    block_number: int
    timestamp: int
    difficulty: int
    base_fee: int
    previous_randao: int | None
    code: tuple[int, ...]
    accounts: tuple[Account, ...]
    expected_storage: tuple[tuple[int, int], ...]
    access_list: tuple[tuple[int, tuple[int, ...]], ...] = ()
    expected_account_storage: tuple[tuple[int, tuple[tuple[int, int], ...]], ...] = ()
    expected_accounts: tuple[Account, ...] = ()
    expected_logs_hash: int | None = None


SPEC_IDS = {
    "Cancun": "CANCUN",
    "Prague": "PRAGUE",
    "Osaka": "OSAKA",
}


def parse_hex_int(value: Any, field: str) -> int:
    if not isinstance(value, str):
        raise FixtureError(f"{field} must be a hexadecimal string")
    try:
        return int(value, 16)
    except ValueError as error:
        raise FixtureError(f"{field} has invalid hexadecimal value {value!r}") from error


def effective_gas_price(transaction: dict[str, Any], env: dict[str, Any]) -> int:
    if "gasPrice" in transaction:
        if "maxFeePerGas" in transaction or "maxPriorityFeePerGas" in transaction:
            raise FixtureError("transaction mixes legacy and dynamic fee fields")
        return parse_hex_int(transaction["gasPrice"], "transaction.gasPrice")
    cap = parse_hex_int(transaction.get("maxFeePerGas"), "transaction.maxFeePerGas")
    tip = parse_hex_int(transaction.get("maxPriorityFeePerGas"), "transaction.maxPriorityFeePerGas")
    base = parse_hex_int(env.get("currentBaseFee"), "env.currentBaseFee")
    if min(cap, tip, base) < 0 or cap < base or tip > cap:
        raise FixtureError("invalid dynamic fee bounds")
    return min(cap, base + tip)


def parse_hex_bytes(value: Any, field: str) -> tuple[int, ...]:
    if not isinstance(value, str):
        raise FixtureError(f"{field} must be a hexadecimal string")
    digits = value[2:] if value.startswith("0x") else value
    if len(digits) % 2:
        raise FixtureError(f"{field} must contain complete bytes")
    try:
        return tuple(bytes.fromhex(digits))
    except ValueError as error:
        raise FixtureError(f"{field} has invalid hexadecimal value {value!r}") from error


def parse_storage(value: Any, field: str) -> tuple[tuple[int, int], ...]:
    if not isinstance(value, dict):
        raise FixtureError(f"{field} must be an object")
    entries = [
        (
            parse_hex_int(key, f"{field} key"),
            parse_hex_int(entry, f"{field}[{key}]"),
        )
        for key, entry in value.items()
    ]
    return tuple(sorted(entries))


def select_index(values: Any, index: Any, field: str) -> Any:
    if not isinstance(values, list):
        raise FixtureError(f"transaction.{field} must be a list")
    if not isinstance(index, int) or index < 0 or index >= len(values):
        raise FixtureError(f"post case has an invalid {field} index")
    return values[index]


def parse_access_list(value: Any) -> tuple[tuple[int, tuple[int, ...]], ...]:
    if value is None:
        return ()
    if not isinstance(value, list):
        raise FixtureError("selected transaction.accessLists must be a list or null")

    def fixed_hex(text: Any, size: int, field: str) -> int:
        if (
            not isinstance(text, str)
            or not text.startswith("0x")
            or len(text) != 2 + 2 * size
            or any(char not in "0123456789abcdefABCDEF" for char in text[2:])
        ):
            raise FixtureError(f"{field} must be a {size}-byte hexadecimal string")
        return int(text, 16)

    entries = []
    for entry in value:
        if not isinstance(entry, dict):
            raise FixtureError("access-list entry must be an object")
        address = fixed_hex(entry.get("address"), 20, "access-list address")
        keys = entry.get("storageKeys")
        if not isinstance(keys, list):
            raise FixtureError("access-list storageKeys must be a list")
        entries.append((address, tuple(
            fixed_hex(key, 32, "access-list storage key") for key in keys
        )))
    return tuple(entries)


def load_state_case(
    path: Path, fork: str, post_index: int | None = None, *,
    test_name: str | None = None,
) -> StateCase:
    document = json.loads(path.read_text())
    if not isinstance(document, dict):
        raise FixtureError("fixture must be an object")
    if test_name is None:
        if len(document) != 1:
            raise FixtureError("fixture must contain exactly one test")
        name, test = next(iter(document.items()))
    else:
        if test_name not in document:
            raise FixtureError(f"fixture has no test named {test_name!r}")
        name, test = test_name, document[test_name]
    if not isinstance(test, dict):
        raise FixtureError("fixture test must be an object")

    try:
        spec_id = SPEC_IDS[fork]
    except KeyError as error:
        supported = ", ".join(sorted(SPEC_IDS))
        raise FixtureError(f"unsupported fork {fork!r}; supported: {supported}") from error

    config = test.get("config", {})
    env = test.get("env", {})
    pre = test.get("pre", {})
    transaction = test.get("transaction", {})
    post_cases = test.get("post", {}).get(fork)
    if not isinstance(config, dict) or not isinstance(env, dict):
        raise FixtureError("fixture config and env must be objects")
    if not isinstance(pre, dict) or not isinstance(transaction, dict):
        raise FixtureError("fixture pre and transaction must be objects")
    if not isinstance(post_cases, list) or not post_cases:
        raise FixtureError(f"fixture must contain post cases for {fork}")
    if post_index is None and len(post_cases) != 1:
        raise FixtureError(f"fixture must contain exactly one post case for {fork}")
    if post_index is None:
        post_index = 0
    if not isinstance(post_index, int) or not 0 <= post_index < len(post_cases):
        raise FixtureError("invalid post case index")
    post_case = post_cases[post_index]
    indexes = post_case.get("indexes", {})
    if not isinstance(indexes, dict):
        raise FixtureError("post case indexes must be an object")
    calldata_hex = select_index(
        transaction.get("data"), indexes.get("data"), "data"
    )
    transaction_gas_limit_hex = select_index(
        transaction.get("gasLimit"), indexes.get("gas"), "gasLimit"
    )
    call_value_hex = select_index(
        transaction.get("value"), indexes.get("value"), "value"
    )
    access_list = ()
    if "accessLists" in transaction:
        access_lists = transaction["accessLists"]
        if not isinstance(access_lists, list) or len(access_lists) != len(transaction["data"]):
            raise FixtureError("transaction.accessLists must match transaction.data length")
        access_list = parse_access_list(select_index(
            access_lists, indexes.get("data"), "accessLists"
        ))

    target_hex = transaction.get("to")
    caller_hex = transaction.get("sender")
    target_address = parse_hex_int(target_hex, "transaction.to")
    caller_address = parse_hex_int(caller_hex, "transaction.sender")
    target_key = next(
        (key for key in pre if key.lower() == str(target_hex).lower()),
        None,
    )
    if target_key is None:
        raise FixtureError("transaction target is missing from the pre-state")

    accounts = []
    for address_hex, value in pre.items():
        if not isinstance(value, dict):
            raise FixtureError(f"pre-state account {address_hex} must be an object")
        address = parse_hex_int(address_hex, f"pre-state address {address_hex}")
        accounts.append(
            Account(
                address=address,
                balance=parse_hex_int(value.get("balance"), f"{address_hex}.balance"),
                nonce=parse_hex_int(value.get("nonce"), f"{address_hex}.nonce"),
                code=parse_hex_bytes(value.get("code"), f"{address_hex}.code"),
                storage=parse_storage(
                    value.get("storage"), f"{address_hex}.storage"
                ),
            )
        )

    post_state = post_case.get("state", {})
    if not isinstance(post_state, dict):
        raise FixtureError("post case state must be an object")
    post_target = next(
        (value for key, value in post_state.items() if key.lower() == str(target_hex).lower()),
        None,
    )
    if not isinstance(post_target, dict):
        raise FixtureError("transaction target is missing from the post-state")

    target = pre[target_key]
    previous_randao_value = env.get("currentRandom")
    previous_randao = (
        parse_hex_int(previous_randao_value, "env.currentRandom")
        if previous_randao_value is not None
        else None
    )
    expected_storage = parse_storage(
        post_target.get("storage"), f"post-state {target_key}.storage"
    )
    expected_logs_hash = None
    if path in LOG_FIXTURES:
        log_hash = parse_hex_bytes(post_case.get("logs"), "post.logs")
        if len(log_hash) != 32:
            raise FixtureError("post.logs must contain exactly 32 bytes")
        expected_logs_hash = int.from_bytes(bytes(log_hash), "big")
    expected_accounts = ()
    if path in ACCOUNT_STATE_FIXTURES:
        if any(not isinstance(account, dict) for account in post_state.values()):
            raise FixtureError("post-state accounts must be objects")
        sender = next((account for account in accounts
                       if account.address == caller_address), None)
        coinbase = parse_hex_int(env.get("currentCoinbase"), "env.currentCoinbase")
        if (parse_hex_int(call_value_hex, "selected transaction.value") != 0
                or caller_address in (target_address, coinbase)
                or sender is None or sender.code):
            raise FixtureError("account checks require zero entry value and an "
                               "uncoded sender distinct from target and coinbase")
        expected_accounts = tuple(sorted((
            Account(
                address=parse_hex_int(address, "post-state address"),
                balance=parse_hex_int(account.get("balance"), "post-state balance"),
                nonce=parse_hex_int(account.get("nonce"), "post-state nonce"),
                code=parse_hex_bytes(account.get("code"), "post-state code"),
                storage=parse_storage(account.get("storage"), "post-state storage"),
            ) for address, account in post_state.items()
        ), key=lambda account: account.address))
    return StateCase(
        name=name,
        fork=fork,
        spec_id=spec_id,
        target_address=target_address,
        caller_address=caller_address,
        chain_id=parse_hex_int(config.get("chainid"), "config.chainid"),
        gas_price=effective_gas_price(transaction, env),
        transaction_gas_limit=parse_hex_int(
            transaction_gas_limit_hex,
            "selected transaction.gasLimit",
        ),
        transaction_nonce=parse_hex_int(
            transaction.get("nonce"), "transaction.nonce"
        ),
        call_value=parse_hex_int(call_value_hex, "selected transaction.value"),
        calldata=parse_hex_bytes(calldata_hex, "selected transaction.data"),
        coinbase=parse_hex_int(env.get("currentCoinbase"), "env.currentCoinbase"),
        gas_limit=parse_hex_int(env.get("currentGasLimit"), "env.currentGasLimit"),
        block_number=parse_hex_int(env.get("currentNumber"), "env.currentNumber"),
        timestamp=parse_hex_int(env.get("currentTimestamp"), "env.currentTimestamp"),
        difficulty=parse_hex_int(env.get("currentDifficulty"), "env.currentDifficulty"),
        base_fee=parse_hex_int(env.get("currentBaseFee"), "env.currentBaseFee"),
        previous_randao=previous_randao,
        code=parse_hex_bytes(target.get("code"), f"{target_key}.code"),
        accounts=tuple(sorted(accounts, key=lambda account: account.address)),
        expected_storage=expected_storage,
        expected_accounts=expected_accounts,
        expected_logs_hash=expected_logs_hash,
        access_list=access_list,
        expected_account_storage=tuple(sorted(
            (parse_hex_int(address, "post-state address"),
             parse_storage(account.get("storage"), f"post-state {address}.storage"))
            for address, account in post_state.items()
        )) if path in CALL_EXECUTION_FIXTURES else (),
    )


def make_exceptional_halt_case(fork: str) -> StateCase:
    case = load_state_case(ADD11_FIXTURE, fork)
    code = (0x60, 0x01, 0x60, 0x00, 0x55, 0x00)
    accounts = tuple(
        replace(account, code=code)
        if account.address == case.target_address
        else account
        for account in case.accounts
    )
    return replace(
        case,
        name="sstore_out_of_gas_before_stop",
        transaction_gas_limit=2400,
        code=code,
        accounts=accounts,
        expected_storage=next(account.storage for account in accounts
                              if account.address == case.target_address),
    )


def render_list(values: tuple[int, ...]) -> str:
    return "[" + "; ".join(str(value) for value in values) + "]"


def render_u8_list(values: tuple[int, ...]) -> str:
    return "[" + "; ".join(f"({value} : u8)" for value in values) + "]"


def load_state_cases(path: Path, fork: str) -> tuple[StateCase, ...]:
    path = path.resolve()
    raw = path.read_bytes()
    if path in OSAKA_SELECTION:
        if fork != "Osaka":
            raise FixtureError("Osaka selection requires Osaka post-states")
        digest, expected_count = OSAKA_SELECTION[path]
        if hashlib.sha256(raw).hexdigest() != digest:
            raise FixtureError("Osaka fixture differs from the pinned audited file")
        document = json.loads(raw)
        if not isinstance(document, dict) or len(document) != expected_count:
            raise FixtureError("Osaka fixture has an unexpected named-test count")
        cases = []
        for name, test in document.items():
            posts = test.get("post", {}).get("Osaka") if isinstance(test, dict) else None
            if not isinstance(posts, list) or len(posts) != 1:
                raise FixtureError("each selected Osaka test must have exactly one post case")
            cases.append(load_state_case(path, fork, 0, test_name=name))
        return tuple(cases)
    selection = MODEXP_SELECTION.get(path)
    if selection is not None:
        if fork not in ("Cancun", "Prague"):
            raise FixtureError("MODEXP selection supports only Cancun and Prague")
        if hashlib.sha256(raw).hexdigest() != selection[0]:
            raise FixtureError("MODEXP fixture differs from the pinned audited file")
    document = json.loads(raw)
    if not isinstance(document, dict) or len(document) != 1:
        raise FixtureError("fixture must contain exactly one test")
    test = next(iter(document.values()))
    if not isinstance(test, dict):
        raise FixtureError("fixture test must be an object")
    post_cases = test.get("post", {}).get(fork)
    if not isinstance(post_cases, list) or not post_cases:
        raise FixtureError(f"fixture must contain post cases for {fork}")
    return tuple(
        load_state_case(path, fork, index)
        for index in (selection[1] if selection is not None else range(len(post_cases)))
    )


def render_pairs(values: tuple[tuple[int, int], ...]) -> str:
    return "[" + "; ".join(f"({key}, {value})" for key, value in values) + "]"


def render_account(index: int, account: Account) -> str:
    code_hash = keccak.new(digest_bits=256, data=bytes(account.code)).digest()
    return f"""Definition fixture_account_{index} : StatefulHost.Account.t := {{|
  StatefulHost.Account.address := {account.address};
  StatefulHost.Account.balance := {account.balance};
  StatefulHost.Account.nonce := {account.nonce};
  StatefulHost.Account.code := {render_list(account.code)};
  StatefulHost.Account.code_hash := {int.from_bytes(code_hash, "big")};
  StatefulHost.Account.storage := {render_pairs(account.storage)};
  StatefulHost.Account.transient_storage := [];
|}}.

"""


def initial_warm_accounts(case: StateCase) -> tuple[int, ...]:
    # All selected forks include EIP-2929 and EIP-3651. Prague adds BLS
    # addresses 11 through 17; Osaka also activates P256VERIFY at 0x100.
    precompile_count = {"Cancun": 10, "Prague": 17, "Osaka": 17}[case.fork]
    return tuple(dict.fromkeys((
        case.caller_address, case.target_address, case.coinbase,
        *range(1, precompile_count + 1),
        *((256,) if case.fork == "Osaka" else ()),
    )))


def render_rocq(
    path: Path,
    case: StateCase,
    expected_instruction_result: str | None = None,
    expected_output: tuple[int, ...] | None = None,
) -> str:
    if path in OSAKA_FIXTURES:
        if case.fork != "Osaka" or case.spec_id != "OSAKA":
            raise FixtureError("Osaka fixture requires the Osaka interpreter fork")
        if case.call_value != 0:
            raise FixtureError("Osaka fixture requires zero transaction entry value")
        if path == OSAKA_GAS_FIXTURE:
            if expected_instruction_result not in (None, "Stop"):
                raise FixtureError("Osaka gas fixture requires exact Stop terminal result")
            expected_instruction_result = "Stop"
        elif expected_instruction_result is not None:
            raise FixtureError("Osaka memory fixtures require successful bytecode completion")
    if path in ACCOUNT_STATE_FIXTURES and not case.expected_accounts:
        raise FixtureError("account checks require an explicit post-state")
    if path in SELFDESTRUCT_FIXTURES:
        required_result = "SelfDestruct" if path in SELFDESTRUCT_DIRECT_FIXTURES else "Stop"
        if expected_instruction_result not in (None, required_result):
            raise FixtureError("SELFDESTRUCT fixture requires its exact terminal result")
        expected_instruction_result = required_result
    if path in IDENTITY_FIXTURES:
        if expected_instruction_result not in (None, "Stop"):
            raise FixtureError("identity fixture requires exact Stop terminal result")
        expected_instruction_result = "Stop"
    if path in SHA256_FIXTURES:
        if expected_instruction_result not in (None, "Stop"):
            raise FixtureError("SHA256 fixture requires exact Stop terminal result")
        expected_instruction_result = "Stop"
    if path in RIPEMD160_FIXTURES:
        if expected_instruction_result not in (None, "Stop"):
            raise FixtureError("RIPEMD160 fixture requires exact Stop terminal result")
        expected_instruction_result = "Stop"
    if path in MODEXP_FIXTURES:
        if expected_instruction_result not in (None, "Stop"):
            raise FixtureError("MODEXP fixture requires exact Stop terminal result")
        expected_instruction_result = "Stop"
    if path == MCOPY_FIXTURE:
        if case.call_value != 0:
            raise FixtureError("MCOPY fixture requires zero transaction entry value")
        if expected_instruction_result not in (None, "Stop"):
            raise FixtureError("MCOPY fixture requires exact Stop terminal result")
        expected_instruction_result = "Stop"
    if path in LOG_FIXTURES and case.expected_logs_hash is None:
        raise FixtureError("log checks require an explicit expected log hash")
    log_check = (
        f"Z.eqb (LogObservation.hash host.(StatefulHost.logs)) {case.expected_logs_hash}"
        if case.expected_logs_hash is not None else "true"
    )
    log_import = (
        "Require Import revm.revm_interpreter.tests.log_observation."
        if case.expected_logs_hash is not None else ""
    )
    if (expected_instruction_result in ("Return", "Revert")) != (expected_output is not None):
        raise ValueError("Return/Revert checks require explicit expected output bytes")
    output_result = "Revert" if expected_instruction_result == "Revert" else "Return"
    execution = (
        f"CallRunner.run {EXECUTION_FUEL} initial_state"
        if path in CALL_EXECUTION_FIXTURES else
        "StatefulFrame.finish\n"
        "      (InstructionContext.State.host StatefulHost.t WIRE WIRE_types initial_state)\n"
        "    (InterpreterDispatch.run_plain_stateful_fuel\n"
        f"      {EXECUTION_FUEL}\n"
        "      InterpreterTypes.I\n      fixture_should_continue\n"
        "      table\n      initial_state)"
    )
    expected_accounts = "[" + "; ".join(
        f"({address}, {render_pairs(storage)})"
        for address, storage in case.expected_account_storage
    ) + "]"
    account_state_definitions = "".join(
        render_account(index, account).replace("fixture_account_", "fixture_expected_account_")
        for index, account in enumerate(case.expected_accounts)
    )
    expected_account_names = "[" + "; ".join(
        f"fixture_expected_account_{index}" for index in range(len(case.expected_accounts))
    ) + "]"
    output_values = "[" + "; ".join(str(value) for value in expected_output or ()) + "]"
    warm_accounts = "[" + "; ".join(map(str, initial_warm_accounts(case))) + "]"
    access_list = "[" + "; ".join(
        f"({address}, [" + "; ".join(map(str, keys)) + "])"
        for address, keys in case.access_list
    ) + "]"
    output_rejection_goals = ""
    if expected_output is not None:
        incorrect_outputs = [expected_output + (0,)]
        if expected_output:
            incorrect_outputs.extend([
                expected_output[:-1],
                (expected_output[0] ^ 1,) + expected_output[1:],
            ])
        for incorrect_output in incorrect_outputs:
            values = "[" + "; ".join(str(value) for value in incorrect_output) + "]"
            output_rejection_goals += f"""
Goal run_fixture_with_action (fixture_return_output_matches {values}) = None.
Proof. vm_compute. reflexivity. Qed.
"""
    account_names = "; ".join(
        f"fixture_account_{index}" for index in range(len(case.accounts))
    )
    previous_randao = (
        f"Some {case.previous_randao}" if case.previous_randao is not None else "None"
    )
    bytecode = render_u8_list(case.code)
    accounts = "".join(
        render_account(index, account)
        for index, account in enumerate(case.accounts)
    )
    if expected_instruction_result is None:
        goal_subject = "run_fixture"
        expected_result = f"Some {render_pairs(case.expected_storage)}"
    elif expected_instruction_result in ("SelfDestruct", "Stop"):
        goal_subject = "run_fixture_exact_halt"
        expected_result = f"Some {render_pairs(case.expected_storage)}"
    elif expected_instruction_result in ("Return", "Revert"):
        goal_subject = "run_fixture_return"
        expected_result = f"Some {render_pairs(case.expected_storage)}"
    elif expected_instruction_result == "OutOfGas":
        goal_subject = "run_fixture_out_of_gas"
        expected_result = f"Some {render_pairs(case.expected_storage)}"
    elif expected_instruction_result == "OutOfOffset":
        goal_subject = "run_fixture_out_of_offset"
        expected_result = f"Some {render_pairs(case.expected_storage)}"
    elif expected_instruction_result == "MemoryOOG":
        goal_subject = "run_fixture_memory_out_of_gas"
        expected_result = f"Some {render_pairs(case.expected_storage)}"
    elif expected_instruction_result == "StackUnderflow":
        goal_subject = "run_fixture_stack_underflow"
        expected_result = f"Some {render_pairs(case.expected_storage)}"
    else:
        raise ValueError(
            f"unsupported expected instruction result {expected_instruction_result!r}"
        )
    return f"""{log_import}
Require Import Stdlib.Lists.List.
Require Import Stdlib.ZArith.ZArith.

Require Import alloy_primitives.links.aliases.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.instructions.simulate.table.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_InterpreterResult.
Require Import revm.revm_interpreter.links.interpreter_action.
Require Import revm.revm_interpreter.links.instruction_result.
Require Import revm.revm_interpreter.simulate.dispatch.
Require Import revm.revm_interpreter.simulate.instruction_context.
Require Import revm.revm_interpreter.tests.interpreter.
Require Import revm.revm_interpreter.tests.interpreter_types.
Require Import revm.revm_interpreter.tests.stateful_dispatch.
Require Import revm.revm_interpreter.tests.frame.
Require Import revm.revm_interpreter.tests.call_runner.
Require Import revm.revm_interpreter.tests.stateful_host.
Require Import revm.revm_primitives.links.hardfork.
Require Import ruint.links.lib.
Require Import simulate.RocqOfRust.

Import ListNotations.
Open Scope Z_scope.

#[local] Existing Instance StatefulHost.IsLink.
#[local] Existing Instance StatefulHost.HostTypesAreLinks.
#[local] Existing Instance StatefulHost.HostForRevmHost.

(** Generated from {path.name}, fork {case.fork}. This executes the contract
    code directly with the fixture target, caller, calldata, and call value.
    Transaction processing does not yet apply intrinsic gas from limit
    {case.transaction_gas_limit}, nonce {case.transaction_nonce}, balance
    changes, or the top-level value transfer. Child CALL transfers are separate. *)
{accounts}Definition fixture_input : StatefulHost.Input.t := {{|
  StatefulHost.Input.block := {{|
    StatefulHost.Environment.Block.coinbase := {case.coinbase};
    StatefulHost.Environment.Block.gas_limit := {case.gas_limit};
    StatefulHost.Environment.Block.number := {case.block_number};
    StatefulHost.Environment.Block.timestamp := {case.timestamp};
    StatefulHost.Environment.Block.difficulty := {case.difficulty};
    StatefulHost.Environment.Block.base_fee := {case.base_fee};
    StatefulHost.Environment.Block.blob_base_fee := 0;
    StatefulHost.Environment.Block.previous_randao := {previous_randao};
    StatefulHost.Environment.Block.hashes := [];
    StatefulHost.Environment.Block.use_state_test_hashes := true;
  |}};
  StatefulHost.Input.transaction := {{|
    StatefulHost.Environment.Transaction.chain_id := {case.chain_id};
    StatefulHost.Environment.Transaction.gas_price := {case.gas_price};
    StatefulHost.Environment.Transaction.blob_hashes := [];
  |}};
  StatefulHost.Input.call := {{|
    StatefulHost.Environment.Call.caller := {case.caller_address};
  |}};
  StatefulHost.Input.state := [{account_names}];
|}}.

Definition fixture_code : list u8 := {bytecode}.

Definition fixture_gas_with_limit (gas : Gas.t) : Gas.t := {{|
  Gas.limit := {{| Integer.value := {case.transaction_gas_limit} |}};
  Gas.memory := gas.(Gas.memory);
  Gas.refunded := gas.(Gas.refunded);
  Gas.remaining := {{| Integer.value := {case.transaction_gas_limit} |}};
|}}.

Definition fixture_interpreter_input : Input.t := {{|
  Input.target_address :=
    {{| alloy_primitives.bits.links.address.Address.value :=
         {case.target_address} |}};
  Input.caller_address :=
    {{| alloy_primitives.bits.links.address.Address.value :=
         {case.caller_address} |}};
  Input.input :=
    revm.revm_interpreter.interpreter_action.links.call_inputs.CallInput.Bytes {{|
      alloy_primitives.bytes.links.mod.Bytes.value :=
        {{| bytes.Bytes.value :=
             {render_u8_list(case.calldata)} |}};
    |}};
  Input.call_value :=
    {{| ruint.links.lib.Uint.value := {case.call_value} |}};
|}}.

Definition fixture_interpreter_with_input
    (interpreter : Interpreter.t WIRE WIRE_types)
    (input : Input.t) :
    Interpreter.t WIRE WIRE_types := {{|
  Interpreter.bytecode := interpreter.(Interpreter.bytecode);
  Interpreter.gas := fixture_gas_with_limit interpreter.(Interpreter.gas);
  Interpreter.stack := interpreter.(Interpreter.stack);
  Interpreter.return_data := interpreter.(Interpreter.return_data);
  Interpreter.memory := interpreter.(Interpreter.memory);
  Interpreter.input := input;
  Interpreter.sub_routine := interpreter.(Interpreter.sub_routine);
  Interpreter.control := {{|
    Control.gas :=
      fixture_gas_with_limit interpreter.(Interpreter.control).(Control.gas);
    Control.instruction_result :=
      interpreter.(Interpreter.control).(Control.instruction_result);
    Control.next_action := interpreter.(Interpreter.control).(Control.next_action);
  |}};
  Interpreter.runtime_flag := interpreter.(Interpreter.runtime_flag);
  Interpreter.extend := interpreter.(Interpreter.extend);
|}}.

Definition fixture_terminated_successfully
    (action : InterpreterAction.t) : bool :=
  match action with
  | InterpreterAction.NewFrame FrameInput.Empty => true
  | InterpreterAction.Return result =>
      match result.(InterpreterResult.result) with
      | InstructionResult.Stop => true
      | _ => false
      end
  | _ => false
  end.

Definition fixture_should_continue (bytecode : Bytecode.t) : bool :=
  match bytecode.(Bytecode.action) with
  | None => bytecode_is_not_end bytecode
  | Some _ => false
  end.

Definition fixture_halted_out_of_gas (action : InterpreterAction.t) : bool :=
  match action with
  | InterpreterAction.Return result =>
      match result.(InterpreterResult.result) with
      | InstructionResult.OutOfGas => true
      | _ => false
      end
  | _ => false
  end.

Definition fixture_storage_accounts : list (Z * list (Z * Z)) := {expected_accounts}.

(** Storage is a map: insertion order is not part of the fixture oracle.
    Keep every nonzero entry, including duplicates, so normalization cannot
    hide an extra key or an inconsistent account representation. *)
Fixpoint fixture_storage_insert (entry : Z * Z) (storage : list (Z * Z)) :
    list (Z * Z) :=
  match storage with
  | [] => [entry]
  | head :: rest =>
      if Z.leb (fst entry) (fst head) then entry :: storage
      else head :: fixture_storage_insert entry rest
  end.

Definition fixture_normalize_storage (storage : list (Z * Z)) : list (Z * Z) :=
  List.fold_right fixture_storage_insert []
    (List.filter (fun entry => negb (Z.eqb (snd entry) 0)) storage).

Module StorageOracleTest.
  Example reordered_storage_matches :
    fixture_normalize_storage [(1, 1); (2, 0); (0, 1)] = [(0, 1); (1, 1)].
  Proof. vm_compute. reflexivity. Qed.

  Example wrong_value_rejected :
    fixture_normalize_storage [(1, 2); (0, 1)] <> [(0, 1); (1, 1)].
  Proof. vm_compute. discriminate. Qed.

  Example extra_key_rejected :
    fixture_normalize_storage [(2, 1); (1, 1); (0, 1)] <> [(0, 1); (1, 1)].
  Proof. vm_compute. discriminate. Qed.

  Example missing_key_rejected :
    fixture_normalize_storage [(1, 1)] <> [(0, 1); (1, 1)].
  Proof. vm_compute. discriminate. Qed.

  Example duplicate_key_rejected :
    fixture_normalize_storage [(1, 1); (0, 1); (1, 1)] <> [(0, 1); (1, 1)].
  Proof. vm_compute. discriminate. Qed.
End StorageOracleTest.

Definition fixture_account_storage_matches (host : StatefulHost.t) : bool :=
  List.forallb (fun entry =>
    let '(address, expected) := entry in
    let actual := match StatefulHost.find_account address host.(StatefulHost.accounts) with
      | Some account => List.filter (fun entry => negb (Z.eqb (snd entry) 0))
          account.(StatefulHost.Account.storage)
      | None => []
      end in
    Nat.eqb (List.length actual) (List.length expected) &&
    List.forallb (fun pair => Z.eqb
      (StatefulHost.lookup_word (fst pair) actual) (snd pair)) expected
  ) fixture_storage_accounts.

{account_state_definitions}
Definition fixture_expected_accounts : list StatefulHost.Account.t := {expected_account_names}.

Fixpoint fixture_list_eqb {{A : Type}} (eqb : A -> A -> bool)
    (left right : list A) : bool :=
  match left, right with
  | [], [] => true
  | x :: xs, y :: ys => eqb x y && fixture_list_eqb eqb xs ys
  | _, _ => false
  end.

Definition fixture_account_fields_match (sender coinbase : Z)
    (expected actual : StatefulHost.Account.t) : bool :=
  let address := expected.(StatefulHost.Account.address) in
  Z.eqb address actual.(StatefulHost.Account.address) &&
  (Z.eqb address sender ||
    Z.eqb expected.(StatefulHost.Account.nonce) actual.(StatefulHost.Account.nonce)) &&
  fixture_list_eqb Z.eqb expected.(StatefulHost.Account.code) actual.(StatefulHost.Account.code) &&
  (Z.eqb address sender || Z.eqb address coinbase ||
    Z.eqb expected.(StatefulHost.Account.balance) actual.(StatefulHost.Account.balance)) &&
  fixture_list_eqb (fun x y => Z.eqb (fst x) (fst y) && Z.eqb (snd x) (snd y))
    (fixture_normalize_storage expected.(StatefulHost.Account.storage))
    (fixture_normalize_storage actual.(StatefulHost.Account.storage)).

Definition fixture_account_nonempty (sender coinbase : Z)
    (account : StatefulHost.Account.t) : bool :=
  negb (fixture_account_fields_match sender coinbase account
    (StatefulHost.empty_account account.(StatefulHost.Account.address))).

Definition fixture_accounts_match (sender coinbase : Z)
    (expected actual : list StatefulHost.Account.t) : bool :=
  List.forallb (fun account =>
    match StatefulHost.find_account account.(StatefulHost.Account.address) actual with
    | Some found => fixture_account_fields_match sender coinbase account found
    | None => negb (fixture_account_nonempty sender coinbase account)
    end) expected &&
  List.forallb (fun account =>
    match StatefulHost.find_account account.(StatefulHost.Account.address) expected with
    | None => negb (fixture_account_nonempty sender coinbase account)
    | Some _ => true
    end) actual.

Definition fixture_account_state_matches (host : StatefulHost.t) : bool :=
  fixture_accounts_match {case.caller_address} {case.coinbase}
    fixture_expected_accounts host.(StatefulHost.accounts).

Module AccountOracleTest.
  Definition contract := (StatefulHost.empty_account 42)
    <| StatefulHost.Account.nonce := 1 |>
    <| StatefulHost.Account.balance := 7 |>
    <| StatefulHost.Account.code := [0; 1] |>.

  Example matching_contract :
    fixture_accounts_match 1 2 [contract] [contract] = true.
  Proof. vm_compute. reflexivity. Qed.

  Example missing_contract_rejected :
    fixture_accounts_match 1 2 [contract] [] = false.
  Proof. vm_compute. reflexivity. Qed.

  Example wrong_code_rejected :
    fixture_accounts_match 1 2 [contract]
      [contract <| StatefulHost.Account.code := [0] |>] = false.
  Proof. vm_compute. reflexivity. Qed.

  Example wrong_nonce_rejected :
    fixture_accounts_match 1 2 [contract]
      [contract <| StatefulHost.Account.nonce := 0 |>] = false.
  Proof. vm_compute. reflexivity. Qed.

  Example wrong_balance_rejected :
    fixture_accounts_match 1 2 [contract]
      [contract <| StatefulHost.Account.balance := 8 |>] = false.
  Proof. vm_compute. reflexivity. Qed.

  Example unexpected_created_account_rejected :
    fixture_accounts_match 1 2 [] [contract] = false.
  Proof. vm_compute. reflexivity. Qed.

  Example unexpected_storage_only_account_rejected :
    fixture_accounts_match 1 2 []
      [(StatefulHost.empty_account 42)
        <| StatefulHost.Account.storage := [(0, 1)] |>] = false.
  Proof. vm_compute. reflexivity. Qed.

  Example unexpected_balance_only_account_rejected :
    fixture_accounts_match 1 2 []
      [(StatefulHost.empty_account 42)
        <| StatefulHost.Account.balance := 1 |>] = false.
  Proof. vm_compute. reflexivity. Qed.

  Example empty_cleanup_not_required :
    fixture_accounts_match 1 2 [] [StatefulHost.empty_account 42] = true.
  Proof. vm_compute. reflexivity. Qed.

  Example fee_only_coinbase_may_be_absent :
    fixture_accounts_match 1 2
      [(StatefulHost.empty_account 2) <| StatefulHost.Account.balance := 9 |>]
      [] = true.
  Proof. vm_compute. reflexivity. Qed.

  Example coinbase_code_is_still_checked :
    fixture_accounts_match 1 2
      [(StatefulHost.empty_account 2) <| StatefulHost.Account.code := [0] |>]
      [] = false.
  Proof. vm_compute. reflexivity. Qed.

  Example transaction_sender_fields_excluded :
    fixture_accounts_match 1 2
      [(StatefulHost.empty_account 1) <| StatefulHost.Account.nonce := 9 |>
        <| StatefulHost.Account.balance := 7 |>]
      [StatefulHost.empty_account 1] = true.
  Proof. vm_compute. reflexivity. Qed.
End AccountOracleTest.

Definition run_fixture_with_action
    (accept_action : InterpreterAction.t -> bool) :
    option (list (Z * Z)) :=
  let interpreter : Interpreter.t WIRE WIRE_types :=
    make_interpreter_with_bytecode fixture_code {{| Stack.value := [] |}} in
  let interpreter :=
    interpreter_with_spec_id interpreter SpecId.{case.spec_id} in
  let interpreter :=
    fixture_interpreter_with_input interpreter fixture_interpreter_input in
  let initial_state :
      InstructionContext.State.t StatefulHost.t WIRE WIRE_types := {{|
    InstructionContext.State.interpreter := interpreter;
    InstructionContext.State.host :=
      StatefulHost.warm_access_list
        (List.fold_left StatefulHost.warm_account {warm_accounts}
          (StatefulHost.make fixture_input))
        {access_list};
  |}} in
  let table :=
    FragmentInstructionTable.table
      (H := StatefulHost.t)
      (H_types := StatefulHost.host_types)
      (run_host := run_Host_for_StatefulHost)
      run_InterpreterTypes_for_WIRE in
  match
    {execution}
  with
  | Some (action, {{|
      InstructionContext.State.interpreter := _;
      InstructionContext.State.host := host
    |}}) =>
      if accept_action action && fixture_account_storage_matches host &&
          {"fixture_account_state_matches host" if case.expected_accounts else "true"} &&
          {log_check} then
        match
          StatefulHost.find_account
            {case.target_address}
            host.(StatefulHost.accounts)
        with
        | Some account =>
            Some
              (fixture_normalize_storage account.(StatefulHost.Account.storage))
        | None => None
        end
      else None
  | None => None
  end.

Definition run_fixture : option (list (Z * Z)) :=
  run_fixture_with_action fixture_terminated_successfully.

Definition run_fixture_exact_halt : option (list (Z * Z)) :=
  run_fixture_with_action (fun action =>
    match action with
    | InterpreterAction.Return result =>
        match result.(InterpreterResult.result) with
        | InstructionResult.{expected_instruction_result if expected_instruction_result in ("SelfDestruct", "Stop") else "Stop"} => true
        | _ => false
        end
    | _ => false
    end).

Definition run_fixture_out_of_gas : option (list (Z * Z)) :=
  run_fixture_with_action fixture_halted_out_of_gas.

Definition run_fixture_out_of_offset : option (list (Z * Z)) :=
  run_fixture_with_action
    (fun action =>
      match action with
      | InterpreterAction.Return result =>
          match result.(InterpreterResult.result) with
          | InstructionResult.OutOfOffset => true
          | _ => false
          end
      | _ => false
      end).

Definition run_fixture_memory_out_of_gas : option (list (Z * Z)) :=
  run_fixture_with_action
    (fun action =>
      match action with
      | InterpreterAction.Return result =>
          match result.(InterpreterResult.result) with
          | InstructionResult.MemoryOOG => true
          | _ => false
          end
      | _ => false
      end).

Definition fixture_return_output_matches
    (expected_output : list Z) (action : InterpreterAction.t) : bool :=
      match action with
      | InterpreterAction.Return result =>
          match result.(InterpreterResult.result) with
          | InstructionResult.{output_result} =>
              if List.list_eq_dec Z.eq_dec
                (List.map (fun value : u8 => value.(Integer.value))
                  result.(InterpreterResult.output)
                    .(alloy_primitives.bytes.links.mod.Bytes.value).(bytes.Bytes.value))
                expected_output
              then true else false
          | _ => false
          end
      | _ => false
      end.

Definition run_fixture_stack_underflow : option (list (Z * Z)) :=
  run_fixture_with_action
    (fun action =>
      match action with
      | InterpreterAction.Return result =>
          match result.(InterpreterResult.result) with
          | InstructionResult.StackUnderflow => true
          | _ => false
          end
      | _ => false
      end).

Definition run_fixture_return : option (list (Z * Z)) :=
  run_fixture_with_action (fixture_return_output_matches {output_values}).

Goal
  {goal_subject} =
  {expected_result}.
Proof.
  vm_compute.
  reflexivity.
Qed.
{output_rejection_goals}
"""


def run_coqc(source: Path) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [
            "coqc",
            "-R",
            str(ROCQ_ROOT),
            "RocqOfRust",
            "-I",
            str(ROCQ_ROOT / "plugin"),
            "-impredicative-set",
            str(source),
        ],
        cwd=ROCQ_ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
    )


def check_exceptional_halt_regression(directory: Path, fork: str) -> int:
    case = make_exceptional_halt_case(fork)
    generated_path = directory / "ExceptionalHaltTest.v"
    generated_path.write_text(
        render_rocq(
            ADD11_FIXTURE,
            case,
            expected_instruction_result="OutOfGas",
        )
    )
    result = run_coqc(generated_path)
    if result.returncode != 0:
        print(result.stdout, file=sys.stderr, end="")
        return result.returncode
    print("checked that REVM SSTORE out-of-gas is not hidden by trailing STOP")
    return 0


def make_access_list_gas_cases(fork: str) -> tuple[StateCase, ...]:
    base = load_state_case(BALANCE_GAS_FIXTURE, fork)
    code = (0x5A, 0x60, 0, 0x52, 0x60, 42, 0x31, 0x50,
            0x5A, 0x60, 0, 0x51, 0x03, 0x60, 1, 0x55, 0)
    entry = {"address": f"0x{42:040x}", "storageKeys": []}
    return tuple(
        replace(base, name=name, code=code, access_list=parse_access_list(entries),
                expected_storage=((1, cost),))
        for name, entries, cost in (
            ("access_list_cold_balance", [], 2616),
            ("access_list_warm_balance", [entry], 116),
            ("access_list_duplicate_balance", [entry, entry], 116),
        )
    )


def make_code_hash_gas_cases(fork: str) -> tuple[StateCase, ...]:
    cases = tuple(
        replace(case, name=case.name.replace("balance", "code_hash"),
                code=case.code[:6] + (0x3F,) + case.code[7:])
        for case in make_access_list_gas_cases(fork)
    )
    cold = cases[0]
    # Warm the same address through a different instruction before measuring.
    return cases + tuple(
        replace(cold, name=name, code=prefix + cold.code,
                expected_storage=((1, 116),))
        for name, prefix in (
            ("size_then_hash", (0x60, 42, 0x3B, 0x50)),
            ("copy_then_hash", (0x60, 0, 0x60, 0, 0x60, 0, 0x60, 42, 0x3C)),
        )
    )


def check_access_list_regressions(directory: Path, fork: str) -> int:
    cases = make_access_list_gas_cases(fork) + make_code_hash_gas_cases(fork)
    for index, case in enumerate(cases):
        source = directory / f"AccessListGasTest{index}.v"
        source.write_text(render_rocq(BALANCE_GAS_FIXTURE, case))
        result = run_coqc(source)
        if result.returncode != 0:
            print(result.stdout, file=sys.stderr, end="")
            return result.returncode
    print("checked BALANCE/EXTCODEHASH access-list gas and cross-instruction warming")
    return 0


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Compile an Ethereum state fixture against the Rocq REVM dispatcher"
    )
    parser.add_argument(
        "--fixture",
        type=Path,
        action="append",
        help="fixture to check; may be given more than once",
    )
    parser.add_argument("--fork", default="Cancun")
    parser.add_argument("--emit", type=Path, help="write the generated Rocq source here")
    return parser.parse_args()


def select_fixtures(args: argparse.Namespace) -> tuple[Path, ...]:
    fixtures = tuple(args.fixture or ())
    if args.fork == "Osaka" and not fixtures:
        return (OSAKA_GAS_FIXTURE,) if args.emit else OSAKA_FIXTURES
    if args.emit and not fixtures:
        return (ADD11_FIXTURE,)
    if not fixtures:
        for directory, expected in ((SHIFT_FIXTURE_ROOT, 42), (CHAIN_ID_FIXTURE_ROOT, 2),
                                    (SLOAD_FIXTURE_ROOT, 1), (LOG_FIXTURE_ROOT, 46)):
            actual = len(tuple(directory.glob("*.json")))
            if actual != expected:
                raise FixtureError(
                    f"incomplete REVM fixtures in {directory}: expected {expected} JSON files, "
                    f"found {actual}; set REVM_FIXTURE_ROOT to the pinned GeneralStateTests directory"
                )
    return fixtures or DEFAULT_FIXTURES


def main() -> int:
    args = parse_args()
    try:
        fixtures = select_fixtures(args)
        for fixture in fixtures:
            if not fixture.is_file():
                raise FixtureError(f"missing REVM fixture: {fixture}; set REVM_FIXTURE_ROOT to the pinned GeneralStateTests directory")
        if args.emit and len(fixtures) != 1:
            raise FixtureError("--emit requires exactly one --fixture")

        with tempfile.TemporaryDirectory(
            prefix="rocq-revm-state-fixture-"
        ) as directory:
            temporary_directory = Path(directory)
            # These synthetic regressions derive from historical fixtures with
            # Cancun/Prague post-states. The bounded Osaka batch uses its own
            # pinned expectations instead of relabelling those fixtures.
            if not args.emit and args.fork != "Osaka":
                result = check_exceptional_halt_regression(
                    temporary_directory,
                    args.fork,
                )
                if result != 0:
                    return result
                result = check_access_list_regressions(temporary_directory, args.fork)
                if result != 0:
                    return result
            for index, fixture_argument in enumerate(fixtures):
                fixture = fixture_argument.resolve()
                cases = load_state_cases(fixture, args.fork)
                if args.emit and len(cases) != 1:
                    raise FixtureError("--emit requires a fixture with one post case")
                expected_halt = (
                    "OutOfOffset" if fixture in RETURN_DATA_FAILURE_FIXTURES else None
                )
                if fixture in MEMORY_COPY_FAILURE_FIXTURES:
                    expected_halt = "MemoryOOG"
                post_indices = (
                    MODEXP_SELECTION[fixture][1] if fixture in MODEXP_SELECTION
                    else range(len(cases))
                )
                for post_index, case in zip(post_indices, cases):
                    expected_output = None
                    if fixture == MEMORY_RETURN_FIXTURE:
                        expected_halt = "Return"
                        expected_output = case.calldata + (0,) * (-len(case.calldata) % 32)
                    elif fixture == STATIC_RETURN_FIXTURE:
                        expected_halt = "Return"
                        # Child returns 0x15 into byte 31; parent returns bytes 30..31.
                        expected_output = (0, 21)
                    elif fixture == REVERT_FIXTURE:
                        expected_halt = "Revert"
                        expected_output = (0,)
                    elif fixture == REVERT_UNDERFLOW_FIXTURE:
                        expected_halt = "StackUnderflow"
                    source = render_rocq(fixture, case, expected_halt, expected_output)
                    generated_path = (
                        args.emit.resolve()
                        if args.emit
                        else temporary_directory / f"StateFixtureTest{index}_{post_index}.v"
                    )
                    generated_path.write_text(source)
                    result = run_coqc(generated_path)
                    if result.returncode != 0:
                        print(result.stdout, file=sys.stderr, end="")
                        return result.returncode
                    print(
                        f"checked Rocq REVM state fixture {case.name} "
                        f"from {fixture.name}, fork {case.fork}, "
                        f"post case {0 if fixture in OSAKA_SELECTION else post_index}"
                    )
        return 0
    except (FixtureError, OSError, ValueError, json.JSONDecodeError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
