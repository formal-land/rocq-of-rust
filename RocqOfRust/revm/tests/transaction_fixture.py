"""Normalize complete state-test transactions for the Rocq/native REVM boundary.

This adapter does not execute transactions or recover/validate signatures. The
caller in its execution input is the fixture's declared sender. Authentication
provenance is explicit and must accompany any subsequent result classification.
"""

from __future__ import annotations

import copy
import json
from pathlib import Path


class FixtureError(ValueError):
    pass


SCHEMA_VERSION = 1
SUPPORTED_FORKS = {
    "Frontier", "Homestead", "TangerineWhistle", "SpuriousDragon", "Byzantium",
    "ConstantinopleFix", "Istanbul", "Berlin", "London", "Paris", "Shanghai",
    "Cancun", "Prague", "Osaka",
}
LONDON_FORKS = {"London", "Paris", "Shanghai", "Cancun", "Prague", "Osaka"}
MERGE_FORKS = {"Paris", "Shanghai", "Cancun", "Prague", "Osaka"}
BLOB_FORKS = {"Cancun", "Prague", "Osaka"}
HEX_DIGITS = frozenset("0123456789abcdefABCDEF")
MASK_64 = (1 << 64) - 1
KECCAK_ROTATIONS = (
    (0, 36, 3, 41, 18), (1, 44, 10, 45, 2), (62, 6, 43, 15, 61),
    (28, 55, 25, 21, 56), (27, 20, 39, 8, 14),
)
KECCAK_ROUND_CONSTANTS = (
    0x0000000000000001, 0x0000000000008082, 0x800000000000808A,
    0x8000000080008000, 0x000000000000808B, 0x0000000080000001,
    0x8000000080008081, 0x8000000000008009, 0x000000000000008A,
    0x0000000000000088, 0x0000000080008009, 0x000000008000000A,
    0x000000008000808B, 0x800000000000008B, 0x8000000000008089,
    0x8000000000008003, 0x8000000000008002, 0x8000000000000080,
    0x000000000000800A, 0x800000008000000A, 0x8000000080008081,
    0x8000000000008080, 0x0000000080000001, 0x8000000080008008,
)


def keccak256(data: bytes) -> bytes:
    """Legacy Ethereum Keccak-256, with Keccak padding (not SHA3 padding)."""
    state = [0] * 25
    padded = bytearray(data)
    pad_length = 136 - len(padded) % 136
    padded.extend(b"\x00" * pad_length)
    padded[len(data)] ^= 1
    padded[-1] ^= 128
    for offset in range(0, len(padded), 136):
        for lane in range(17):
            state[lane] ^= int.from_bytes(padded[offset + 8 * lane:offset + 8 * lane + 8], "little")
        for constant in KECCAK_ROUND_CONSTANTS:
            columns = [state[x] ^ state[x + 5] ^ state[x + 10] ^ state[x + 15] ^ state[x + 20]
                       for x in range(5)]
            for x in range(5):
                right = columns[(x + 1) % 5]
                delta = columns[(x - 1) % 5] ^ ((right << 1 | right >> 63) & MASK_64)
                for y in range(5):
                    state[x + 5 * y] ^= delta
            rotated = [0] * 25
            for x in range(5):
                for y in range(5):
                    lane = state[x + 5 * y]
                    rotation = KECCAK_ROTATIONS[x][y]
                    rotated[y + 5 * ((2 * x + 3 * y) % 5)] = (
                        (lane << rotation | lane >> ((64 - rotation) % 64)) & MASK_64
                    )
            for x in range(5):
                for y in range(5):
                    state[x + 5 * y] = rotated[x + 5 * y] ^ (
                        ~rotated[(x + 1) % 5 + 5 * y] & rotated[(x + 2) % 5 + 5 * y]
                    )
            state[0] ^= constant
    return b"".join(lane.to_bytes(8, "little") for lane in state)[:32]


def object_field(value: object, field: str) -> dict:
    if not isinstance(value, dict):
        raise FixtureError(f"{field} must be an object")
    return value


def hex_bytes(value: object, field: str, width: int | None = None) -> bytes:
    if not isinstance(value, str):
        raise FixtureError(f"{field} must be a hexadecimal string")
    digits = value[2:] if value.startswith("0x") else value
    if len(digits) % 2 or any(char not in HEX_DIGITS for char in digits):
        raise FixtureError(f"{field} must contain complete hexadecimal bytes")
    result = bytes.fromhex(digits)
    if width is not None and len(result) != width:
        raise FixtureError(f"{field} must be exactly {width} bytes")
    return result


def hex_int(value: object, field: str) -> int:
    if not isinstance(value, str):
        raise FixtureError(f"{field} must be a hexadecimal string")
    digits = value[2:] if value.startswith("0x") else value
    if not digits or any(char not in HEX_DIGITS for char in digits):
        raise FixtureError(f"{field} must be an unsigned hexadecimal integer")
    return int(digits, 16)


def optional_int(record: dict, key: str, field: str) -> int | None:
    value = record.get(key)
    return None if value is None else hex_int(value, field)


def select(values: object, index: object, field: str) -> object:
    if not isinstance(values, list):
        raise FixtureError(f"{field} must be an array")
    if type(index) is not int or not 0 <= index < len(values):
        raise FixtureError(f"invalid selected index for {field}")
    return values[index]


def storage_entries(value: object, field: str) -> list[list[int]]:
    storage = object_field(value, field)
    result = []
    seen = set()
    for key, entry in storage.items():
        slot = hex_int(key, f"{field}.key")
        if slot in seen:
            raise FixtureError(f"{field} contains duplicate numeric storage keys")
        seen.add(slot)
        result.append([slot, hex_int(entry, f"{field}[{key}]")])
    return sorted(result)


def accounts(value: object, field: str) -> list[dict]:
    raw = object_field(value, field)
    result = []
    seen = set()
    for address, value in raw.items():
        address_value = int.from_bytes(hex_bytes(address, f"{field}.address", 20), "big")
        if address_value in seen:
            raise FixtureError(f"{field} contains duplicate numeric account addresses")
        seen.add(address_value)
        value = object_field(value, f"{field}[{address}]")
        unknown = set(value) - {"balance", "nonce", "code", "storage"}
        if unknown:
            raise FixtureError(f"{field}[{address}] has unknown account fields: {sorted(unknown)}")
        code = hex_bytes(value.get("code"), f"{field}[{address}].code")
        result.append({
            "address": address_value,
            "balance": hex_int(value.get("balance"), f"{field}[{address}].balance"),
            "nonce": hex_int(value.get("nonce"), f"{field}[{address}].nonce"),
            "code": list(code), "code_hash": int.from_bytes(keccak256(code), "big"),
            "storage": storage_entries(value.get("storage"), f"{field}[{address}].storage"),
            "transient_storage": [],
        })
    return sorted(result, key=lambda account: account["address"])


def access_list(value: object) -> list[list]:
    if not isinstance(value, list):
        raise FixtureError("selected access list must be an array")
    result = []
    for index, item in enumerate(value):
        item = object_field(item, f"access-list[{index}]")
        if set(item) != {"address", "storageKeys"} or not isinstance(item["storageKeys"], list):
            raise FixtureError("access-list entries require address and storageKeys array")
        address = int.from_bytes(hex_bytes(item["address"], "access-list.address", 20), "big")
        keys = [int.from_bytes(hex_bytes(key, "access-list.storageKey", 32), "big")
                for key in item["storageKeys"]]
        result.append([address, keys])
    return result


def decode_rlp(encoded: bytes) -> bytes | list:
    """Decode canonical RLP, including length and trailing-byte checks."""
    def item(offset: int, end: int) -> tuple[bytes | list, int]:
        if offset >= end:
            raise FixtureError("truncated RLP")
        prefix = encoded[offset]
        if prefix < 128:
            return encoded[offset:offset + 1], offset + 1
        is_list = prefix >= 192
        short_base, long_base = (192, 247) if is_list else (128, 183)
        if prefix <= long_base:
            length = prefix - short_base
            start = offset + 1
        else:
            length_width = prefix - long_base
            start = offset + 1 + length_width
            if start > end or encoded[offset + 1] == 0:
                raise FixtureError("invalid RLP length")
            length = int.from_bytes(encoded[offset + 1:start], "big")
            if length < 56:
                raise FixtureError("noncanonical RLP long length")
        finish = start + length
        if finish > end:
            raise FixtureError("truncated RLP payload")
        if not is_list:
            if length == 1 and encoded[start] < 128:
                raise FixtureError("noncanonical RLP single byte")
            return encoded[start:finish], finish
        children = []
        cursor = start
        while cursor < finish:
            child, cursor = item(cursor, finish)
            children.append(child)
        return children, finish
    value, finish = item(0, len(encoded))
    if finish != len(encoded):
        raise FixtureError("trailing RLP bytes")
    return value


def rlp_number(value: object, field: str) -> int:
    if not isinstance(value, bytes) or (value and value[0] == 0):
        raise FixtureError(f"{field} must be a canonical RLP unsigned integer")
    return int.from_bytes(value, "big")


def normalize_authorizations(raw):
    if raw is None:
        return None
    if not isinstance(raw, list):
        raise FixtureError("transaction.authorizationList must be an array")
    result = []
    for entry in raw:
        entry = object_field(entry, "authorization")
        if set(entry) - {"chainId", "address", "nonce", "v", "yParity", "r", "s", "signer"}:
            raise FixtureError("unknown authorization field")
        parity = hex_int(entry.get("yParity", entry.get("v")), "authorization.yParity")
        if "yParity" in entry and "v" in entry and parity != hex_int(entry["v"], "authorization.v"):
            raise FixtureError("authorization parity fields disagree")
        result.append({
            "chain_id": hex_int(entry.get("chainId"), "authorization.chainId"),
            "address": int.from_bytes(hex_bytes(entry.get("address"), "authorization.address", 20), "big"),
            "nonce": hex_int(entry.get("nonce"), "authorization.nonce"),
            "y_parity": parity,
            "r": hex_int(entry.get("r"), "authorization.r"),
            "s": hex_int(entry.get("s"), "authorization.s"),
        })
    return result


def signed_envelope(encoded: bytes) -> dict:
    if not encoded:
        raise FixtureError("empty transaction envelope")
    tx_type = encoded[0] if encoded[0] < 128 else 0
    if tx_type not in (0, 1, 2, 3, 4):
        return {"tx_type": tx_type, "supported": False}
    fields = decode_rlp(encoded[1:] if tx_type else encoded)
    expected = {0: 9, 1: 11, 2: 12, 3: 14, 4: 13}[tx_type]
    if not isinstance(fields, list) or len(fields) != expected:
        raise FixtureError(f"type {tx_type} envelope must have {expected} fields")
    max_blob_fee = 0
    blob_hashes = []
    authorizations = None
    if tx_type == 0:
        nonce, price, gas, target, value, data, parity, r, s = fields
        v = rlp_number(parity, "transaction.v")
        if v in (0, 1, 27, 28):
            chain_id = None
        else:
            # Match Geth and TransactionAuth.legacy_chain_id, including uint64
            # subtraction for invalid small protected-v values such as v=34.
            chain_id = ((v - 35) % (1 << 64)) // 2 if v < 1 << 64 else (v - 35) // 2
        priority = None
        entries = []
    else:
        chain_id = rlp_number(fields[0], "transaction.chain_id")
        if tx_type == 1:
            _, nonce, price, gas, target, value, data, raw_list, parity, r, s = fields
            priority = None
        elif tx_type == 2:
            _, nonce, priority, price, gas, target, value, data, raw_list, parity, r, s = fields
            priority = rlp_number(priority, "transaction.max_priority_fee")
        elif tx_type == 4:
            (_, nonce, priority, price, gas, target, value, data, raw_list,
             raw_authorizations, parity, r, s) = fields
            priority = rlp_number(priority, "transaction.max_priority_fee")
            if not isinstance(raw_authorizations, list):
                raise FixtureError("RLP authorization list must be a list")
            authorizations = []
            for entry in raw_authorizations:
                if not isinstance(entry, list) or len(entry) != 6:
                    raise FixtureError("RLP authorization must have six fields")
                if not isinstance(entry[1], bytes) or len(entry[1]) != 20:
                    raise FixtureError("RLP authorization address must be 20 bytes")
                authorizations.append({
                    key: int.from_bytes(item, "big") if key == "address" else rlp_number(item, "authorization." + key)
                    for key, item in zip(("chain_id", "address", "nonce", "y_parity", "r", "s"), entry)
                })
        else:
            (_, nonce, priority, price, gas, target, value, data, raw_list,
             raw_blob_fee, raw_blob_hashes, parity, r, s) = fields
            priority = rlp_number(priority, "transaction.max_priority_fee")
            max_blob_fee = rlp_number(raw_blob_fee, "transaction.max_fee_per_blob_gas")
            if not isinstance(raw_blob_hashes, list):
                raise FixtureError("RLP blob hashes must be a list")
            if any(not isinstance(hash_value, bytes) or len(hash_value) != 32
                   for hash_value in raw_blob_hashes):
                raise FixtureError("RLP blob hashes must each be 32 bytes")
            blob_hashes = [int.from_bytes(hash_value, "big") for hash_value in raw_blob_hashes]
        if not isinstance(raw_list, list):
            raise FixtureError("RLP access-list must be a list")
        entries = []
        for entry in raw_list:
            if not isinstance(entry, list) or len(entry) != 2 or not isinstance(entry[1], list):
                raise FixtureError("invalid RLP access-list entry")
            address, keys = entry
            if not isinstance(address, bytes) or len(address) != 20:
                raise FixtureError("RLP access-list address must be 20 bytes")
            if any(not isinstance(key, bytes) or len(key) != 32 for key in keys):
                raise FixtureError("RLP access-list keys must be 32 bytes")
            entries.append([int.from_bytes(address, "big"), [int.from_bytes(key, "big") for key in keys]])
    if not isinstance(target, bytes) or len(target) not in (0, 20) or not isinstance(data, bytes):
        raise FixtureError("RLP target/data have invalid shape")
    return {
        "supported": True, "tx_type": tx_type,
        "chain_id": chain_id, "nonce": rlp_number(nonce, "transaction.nonce"),
        "gas_price": rlp_number(price, "transaction.gas_price"), "max_priority_fee": priority,
        "gas_limit": rlp_number(gas, "transaction.gas_limit"),
        "target": int.from_bytes(target, "big") if target else None,
        "value": rlp_number(value, "transaction.value"), "data": list(data),
        "access_list": entries, "max_fee_per_blob_gas": max_blob_fee,
        "blob_hashes": blob_hashes, "authorization_list": authorizations,
        "signature": {"v": rlp_number(parity, "transaction.v"),
                      "r": rlp_number(r, "transaction.r"), "s": rlp_number(s, "transaction.s")},
    }


def fake_exponential(numerator: int, denominator: int) -> int:
    if denominator <= 0:
        raise FixtureError("blob base-fee update fraction must be positive")
    accumulator = denominator
    output = 0
    index = 1
    while accumulator:
        output += accumulator
        accumulator = accumulator * numerator // (denominator * index)
        index += 1
        if output.bit_length() > 4096:
            raise FixtureError("blob base-fee input exceeds computable normalization bounds")
    return output // denominator


def normalize_case(document: object, fork: str, post_index: int | None = None,
                   *, test_name: str | None = None) -> dict:
    document = object_field(document, "fixture")
    if test_name is None:
        if len(document) != 1:
            raise FixtureError("choose test_name for a fixture containing multiple tests")
        test_name = next(iter(document))
    if test_name not in document:
        raise FixtureError(f"fixture has no test {test_name!r}")
    test = object_field(document[test_name], "test")
    config = object_field(test.get("config", {}), "config")
    env = object_field(test.get("env"), "env")
    raw_tx = object_field(test.get("transaction"), "transaction")
    post_cases = object_field(test.get("post"), "post").get(fork)
    if not isinstance(post_cases, list) or not post_cases:
        raise FixtureError(f"fixture has no post cases for {fork}")
    if post_index is None:
        if len(post_cases) != 1:
            raise FixtureError("choose post_index for multiple post cases")
        post_index = 0
    post = object_field(select(post_cases, post_index, "post cases"), "post case")
    indexes = object_field(post.get("indexes"), "post.indexes")
    if set(indexes) != {"data", "gas", "value"}:
        raise FixtureError("post.indexes must contain data, gas and value")
    data = hex_bytes(select(raw_tx.get("data"), indexes["data"], "transaction.data"), "selected data")
    gas_limit = hex_int(select(raw_tx.get("gasLimit"), indexes["gas"], "transaction.gasLimit"), "selected gasLimit")
    value = hex_int(select(raw_tx.get("value"), indexes["value"], "transaction.value"), "selected value")
    selected_access = None
    if raw_tx.get("accessLists") is not None:
        lists = raw_tx["accessLists"]
        if not isinstance(lists, list) or len(lists) != len(raw_tx["data"]):
            raise FixtureError("transaction.accessLists must match data array length")
        selected_access = select(lists, indexes["data"], "transaction.accessLists")
    entries = [] if selected_access is None else access_list(selected_access)
    unsupported = []
    if fork not in SUPPORTED_FORKS:
        unsupported.append(f"fork:{fork}")
    raw_exception = post.get("expectException")
    if raw_exception is not None and not isinstance(raw_exception, str):
        raise FixtureError("post.expectException must be a string")
    exception = raw_exception or None
    txbytes = hex_bytes(post["txbytes"], "post.txbytes") if "txbytes" in post else None
    envelope = None
    envelope_error = None
    if txbytes is not None:
        try:
            envelope = signed_envelope(txbytes)
        except FixtureError as error:
            if exception is None:
                raise
            envelope_error = str(error)
            unsupported.append("invalid_signed_envelope")
    dynamic = "maxFeePerGas" in raw_tx or "maxPriorityFeePerGas" in raw_tx
    if dynamic and "gasPrice" in raw_tx:
        raise FixtureError("transaction mixes legacy and dynamic fee fields")
    if "authorizationList" in raw_tx and raw_tx["authorizationList"] is not None:
        inferred_type = 4
    elif any(key in raw_tx for key in ("blobVersionedHashes", "maxFeePerBlobGas")):
        inferred_type = 3
    elif dynamic:
        inferred_type = 2
    else:
        inferred_type = 1 if selected_access is not None else 0
    explicit_type = optional_int(raw_tx, "type", "transaction.type")
    tx_type = explicit_type if explicit_type is not None else inferred_type
    if envelope is not None:
        if explicit_type is not None and explicit_type != envelope["tx_type"]:
            raise FixtureError("transaction type disagrees with signed envelope")
        if inferred_type != envelope["tx_type"]:
            raise FixtureError("transaction fields disagree with signed envelope type")
        tx_type = envelope["tx_type"]
    if tx_type not in (0, 1, 2, 3, 4):
        unsupported.append(f"transaction_type:{tx_type}")
    target_raw = raw_tx.get("to")
    if target_raw in ("", "0x"):
        target = None
    else:
        target = int.from_bytes(hex_bytes(target_raw, "transaction.to", 20), "big")
    caller = None
    if raw_tx.get("sender") is None:
        unsupported.append("sender_recovery_required")
    else:
        caller = int.from_bytes(hex_bytes(raw_tx["sender"], "transaction.sender", 20), "big")
    tx_chain_id = optional_int(raw_tx, "chainId", "transaction.chainId")
    if envelope is not None and envelope.get("supported"):
        # Legacy v<35 does not bind the construction field chainId. It can be
        # unprotected or deliberately invalid; only the signed v determines the
        # decoded transaction's chain ID. Protected-v and typed IDs are checked.
        binds_chain_id = tx_type != 0 or envelope["signature"]["v"] >= 35
        if binds_chain_id and "chainId" in raw_tx and tx_chain_id != envelope["chain_id"]:
            raise FixtureError("transaction.chainId disagrees with signed envelope")
        tx_chain_id = envelope["chain_id"]
    raw_blobs = raw_tx.get("blobVersionedHashes")
    if raw_blobs is not None and not isinstance(raw_blobs, list):
        raise FixtureError("transaction.blobVersionedHashes must be an array")
    blob_hashes = None if raw_blobs is None else [
        int.from_bytes(hex_bytes(value, "transaction.blobVersionedHashes", 32), "big")
        for value in raw_blobs
    ]
    transaction = {
        "tx_type": tx_type, "caller": caller, "target": target,
        "nonce": hex_int(raw_tx.get("nonce"), "transaction.nonce"),
        "chain_id": tx_chain_id, "gas_limit": gas_limit,
        "gas_price": hex_int(raw_tx.get("maxFeePerGas" if dynamic else "gasPrice"), "transaction.fee_cap"),
        "max_priority_fee": optional_int(raw_tx, "maxPriorityFeePerGas", "transaction.maxPriorityFeePerGas"),
        "access_list": entries, "value": value, "data": list(data),
        "max_fee_per_blob_gas": optional_int(raw_tx, "maxFeePerBlobGas", "transaction.maxFeePerBlobGas") or 0,
        "blob_hashes": blob_hashes or [],
        "authorization_list": normalize_authorizations(raw_tx.get("authorizationList")),
    }
    if envelope is not None and envelope.get("supported"):
        for key in ("tx_type", "nonce", "chain_id", "gas_limit", "gas_price", "max_priority_fee",
                    "target", "value", "data", "access_list", "max_fee_per_blob_gas", "blob_hashes", "authorization_list"):
            if transaction[key] != envelope[key]:
                raise FixtureError(f"selected transaction.{key} disagrees with signed envelope")
    known_tx_fields = {
        "data", "gasLimit", "gasPrice", "maxFeePerGas", "maxPriorityFeePerGas", "nonce", "secretKey",
        "sender", "to", "value", "accessLists", "chainId", "type", "blobVersionedHashes",
        "maxFeePerBlobGas", "authorizationList", "_info",
    }
    meaningful_extras = sorted(set(raw_tx) - known_tx_fields)
    if meaningful_extras:
        unsupported.extend(f"transaction_field:{key}" for key in meaningful_extras)
    known_env_fields = {
        "currentCoinbase", "currentGasLimit", "currentNumber", "currentTimestamp", "currentDifficulty",
        "currentBaseFee", "currentRandom", "currentExcessBlobGas", "currentBlobGasPrice",
        "blockHashes", "previousHash", "_info",
    }
    unsupported.extend(f"environment_field:{key}" for key in sorted(set(env) - known_env_fields))
    unsupported.extend(f"configuration_field:{key}" for key in sorted(set(config) - {"chainid", "blobSchedule", "_info"}))
    if "currentBaseFee" not in env and fork in LONDON_FORKS:
        unsupported.append("base_fee_not_supplied")
    excess = optional_int(env, "currentExcessBlobGas", "env.currentExcessBlobGas")
    fraction = 3338477 if fork == "Cancun" else 5007716
    max_blobs = 6 if fork == "Cancun" else 9
    blob_schedule = config.get("blobSchedule", {})
    if blob_schedule is not None:
        blob_schedule = object_field(blob_schedule, "config.blobSchedule")
        schedule = blob_schedule.get(fork)
        if schedule is None and fork == "Osaka":
            schedule = blob_schedule.get("Prague")
        if schedule is not None:
            schedule = object_field(schedule, f"config.blobSchedule.{fork}")
            fraction = hex_int(schedule.get("baseFeeUpdateFraction"), "blobSchedule.baseFeeUpdateFraction")
            max_blobs = hex_int(schedule.get("max"), "blobSchedule.max")
    # Osaka limits each transaction to six blobs independently of the block schedule.
    if fork == "Osaka":
        max_blobs = 6
    explicit_blob_price = optional_int(env, "currentBlobGasPrice", "env.currentBlobGasPrice")
    blob_price = explicit_blob_price if explicit_blob_price is not None else (
        fake_exponential(excess, fraction) if excess is not None else 0
    )
    if fork not in BLOB_FORKS:
        excess, blob_price, max_blobs = None, 0, None
    block_hashes = env.get("blockHashes", {})
    block = {
        "coinbase": int.from_bytes(hex_bytes(env.get("currentCoinbase"), "env.currentCoinbase", 20), "big"),
        "gas_limit": hex_int(env.get("currentGasLimit"), "env.currentGasLimit"),
        "number": hex_int(env.get("currentNumber"), "env.currentNumber"),
        "timestamp": hex_int(env.get("currentTimestamp"), "env.currentTimestamp"),
        "difficulty": hex_int(env.get("currentDifficulty", "0x0"), "env.currentDifficulty"),
        "base_fee": hex_int(env.get("currentBaseFee", "0x0"), "env.currentBaseFee") if fork in LONDON_FORKS else 0,
        "previous_randao": optional_int(env, "currentRandom", "env.currentRandom") if fork in MERGE_FORKS else None,
        "blob_base_fee": blob_price,
        "hashes": storage_entries(block_hashes, "env.blockHashes"),
        "use_state_test_hashes": True,
    }
    if "previousHash" in env:
        previous = hex_int(env["previousHash"], "env.previousHash")
        if block["number"] == 0:
            raise FixtureError("previousHash requires a nonzero currentNumber")
        if any(number == block["number"] - 1 for number, _ in block["hashes"]):
            raise FixtureError("previousHash overlaps blockHashes")
        block["hashes"].append([block["number"] - 1, previous])
        block["hashes"].sort()
    # Preserve hash-only fixtures without inventing an explicit post-state.
    expected_accounts = accounts(post["state"], "post.state") if "state" in post else None
    # A declared sender is an execution input, never evidence that the signed
    # transaction authenticates it. Every fixture needs actual authentication
    # before a complete pass, regardless of exception names. Missing txbytes
    # provides no signature evidence either; declared-sender execution comparisons
    # remain possible using the separately normalized execution input.
    requires_authentication = True
    blob_creation_forbidden = tx_type == 3 and target is None
    if blob_creation_forbidden:
        # Native normalized TxEnv execution accepts this shape, while canonical
        # EIP-4844 signed transactions require a 20-byte destination. Keep the
        # decoding/validation boundary distinct from native handler execution.
        unsupported.append("canonical_blob_creation_validation_required")
    if requires_authentication:
        unsupported.append("authentication_verification_required")
    return {
        "schema_version": SCHEMA_VERSION, "name": test_name, "fork": fork,
        "post_index": post_index, "indexes": dict(indexes),
        "transaction": transaction,
        "input": {"chain_id": hex_int(config.get("chainid", "0x1"), "config.chainid"),
                  "block": block, "excess_blob_gas": excess, "max_blobs_per_tx": max_blobs,
                  "accounts": accounts(test.get("pre"), "pre")},
        "expectation": {
            "exception": exception, "accounts": expected_accounts,
            "state_root": list(hex_bytes(post["hash"], "post.hash", 32)) if "hash" in post else None,
            "logs_hash": list(hex_bytes(post["logs"], "post.logs", 32)) if "logs" in post else None,
            "txbytes": list(txbytes) if txbytes is not None else None,
        },
        "authentication": {
            "caller_source": "fixture_sender" if caller is not None else "unresolved",
            "signature_recovery_verified": False, "requires_verification": requires_authentication,
            "complete_pass_requires_authentication": requires_authentication,
            "envelope_signature": envelope.get("signature") if envelope else None,
            "envelope_error": envelope_error,
        },
        "canonical_envelope": {"blob_creation_forbidden": blob_creation_forbidden},
        "unsupported": sorted(set(unsupported)),
        "source": {"config": copy.deepcopy(config), "env": copy.deepcopy(env),
                   "transaction": copy.deepcopy(raw_tx), "post": copy.deepcopy(post)},
    }


def load_case(path: Path, fork: str, post_index: int | None = None,
              *, test_name: str | None = None) -> dict:
    try:
        document = json.loads(path.read_text())
    except (OSError, UnicodeError, json.JSONDecodeError) as error:
        raise FixtureError(f"cannot load fixture {path}: {error}") from error
    return normalize_case(document, fork, post_index, test_name=test_name)
