#!/usr/bin/env python3
"""Run fixture-derived tests against the Rocq simulation of REVM instructions."""

from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import Any


ROCQ_ROOT = Path(__file__).resolve().parents[2]
REPO_ROOT = ROCQ_ROOT.parent
FIXTURE_ROOT = Path(os.environ.get(
    "REVM_FIXTURE_ROOT", REPO_ROOT / "tests/revm-testdata/GeneralStateTests"
)).expanduser().resolve()
ARITHMETIC_FIXTURE_ROOT = (
    FIXTURE_ROOT / "VMTests/vmArithmeticTest"
)
BITWISE_FIXTURE_ROOT = (
    FIXTURE_ROOT / "VMTests/vmBitwiseLogicOperation"
)
SSTORE_ZERO_STOP = bytes([0x60, 0x00, 0x55, 0x00])
PUSH_ZERO_SUB = bytes([0x60, 0x00, 0x03])
U256_MODULUS = 1 << 256


class FixtureError(RuntimeError):
    pass


@dataclass(frozen=True)
class Instruction:
    fixture_name: str
    rocq_name: str
    opcode: int
    operand_count: int
    simulation_module: str
    fixture_root: Path
    requires_interpreter_types: bool = False


INSTRUCTIONS = {
    "add": Instruction(
        "add", "add", 0x01, 2, "arithmetic.add", ARITHMETIC_FIXTURE_ROOT
    ),
    "mul": Instruction(
        "mul", "mul", 0x02, 2, "arithmetic.mul", ARITHMETIC_FIXTURE_ROOT
    ),
    "sub": Instruction(
        "sub", "sub", 0x03, 2, "arithmetic.sub", ARITHMETIC_FIXTURE_ROOT
    ),
    "div": Instruction(
        "div", "div", 0x04, 2, "arithmetic.div", ARITHMETIC_FIXTURE_ROOT
    ),
    "sdiv": Instruction(
        "sdiv", "sdiv", 0x05, 2, "arithmetic.sdiv", ARITHMETIC_FIXTURE_ROOT
    ),
    "mod": Instruction(
        "mod", "rem", 0x06, 2, "arithmetic.rem", ARITHMETIC_FIXTURE_ROOT
    ),
    "smod": Instruction(
        "smod", "smod", 0x07, 2, "arithmetic.smod", ARITHMETIC_FIXTURE_ROOT
    ),
    "addmod": Instruction(
        "addmod",
        "addmod",
        0x08,
        3,
        "arithmetic.addmod",
        ARITHMETIC_FIXTURE_ROOT,
    ),
    "mulmod": Instruction(
        "mulmod",
        "mulmod",
        0x09,
        3,
        "arithmetic.mulmod",
        ARITHMETIC_FIXTURE_ROOT,
    ),
    "exp": Instruction(
        "exp",
        "exp",
        0x0A,
        2,
        "arithmetic.exp",
        ARITHMETIC_FIXTURE_ROOT,
        requires_interpreter_types=True,
    ),
    "signextend": Instruction(
        "signextend",
        "signextend",
        0x0B,
        2,
        "arithmetic.signextend",
        ARITHMETIC_FIXTURE_ROOT,
    ),
    "lt": Instruction(
        "lt", "op_lt", 0x10, 2, "bitwise.lt", BITWISE_FIXTURE_ROOT
    ),
    "gt": Instruction(
        "gt", "op_gt", 0x11, 2, "bitwise.gt", BITWISE_FIXTURE_ROOT
    ),
    "slt": Instruction(
        "slt", "op_slt", 0x12, 2, "bitwise.slt", BITWISE_FIXTURE_ROOT
    ),
    "sgt": Instruction(
        "sgt", "op_sgt", 0x13, 2, "bitwise.sgt", BITWISE_FIXTURE_ROOT
    ),
    "eq": Instruction(
        "eq", "op_eq", 0x14, 2, "bitwise.eq", BITWISE_FIXTURE_ROOT
    ),
    "iszero": Instruction(
        "iszero",
        "op_iszero",
        0x15,
        1,
        "bitwise.iszero",
        BITWISE_FIXTURE_ROOT,
    ),
    "and": Instruction(
        "and", "op_bitand", 0x16, 2, "bitwise.bitand", BITWISE_FIXTURE_ROOT
    ),
    "or": Instruction(
        "or", "op_bitor", 0x17, 2, "bitwise.bitor", BITWISE_FIXTURE_ROOT
    ),
    "xor": Instruction(
        "xor", "op_bitxor", 0x18, 2, "bitwise.bitxor", BITWISE_FIXTURE_ROOT
    ),
    "not": Instruction(
        "not", "op_not", 0x19, 1, "bitwise.not", BITWISE_FIXTURE_ROOT
    ),
}


@dataclass(frozen=True)
class InstructionCase:
    instruction: Instruction
    name: str
    operands: tuple[int, ...]
    expected: int


def parse_hex_bytes(value: str) -> bytes:
    if not isinstance(value, str):
        raise FixtureError(f"expected a hexadecimal string, got {value!r}")
    digits = value[2:] if value.startswith("0x") else value
    if len(digits) % 2:
        digits = "0" + digits
    try:
        return bytes.fromhex(digits)
    except ValueError as error:
        raise FixtureError(f"invalid hexadecimal value {value!r}") from error


def decode_push(code: bytes, offset: int) -> tuple[int, int]:
    if offset >= len(code) or not 0x60 <= code[offset] <= 0x7F:
        raise FixtureError(f"expected PUSH instruction at byte {offset}")
    size = code[offset] - 0x5F
    end = offset + 1 + size
    if end > len(code):
        raise FixtureError(f"truncated PUSH instruction at byte {offset}")
    return int.from_bytes(code[offset + 1 : end]), end


def decode_operand(code: bytes, offset: int) -> list[tuple[int, int]]:
    operand, offset = decode_push(code, offset)
    candidates = [(operand, offset)]
    if code[offset : offset + len(PUSH_ZERO_SUB)] == PUSH_ZERO_SUB:
        candidates.append(
            ((-operand) % U256_MODULUS, offset + len(PUSH_ZERO_SUB))
        )
    return candidates


def decode_program(code_hex: str, instruction: Instruction) -> tuple[int, ...]:
    code = parse_hex_bytes(code_hex)

    def decode_operands(
        offset: int,
        remaining: int,
    ) -> tuple[int, ...] | None:
        if remaining == 0:
            if (
                offset < len(code)
                and code[offset] == instruction.opcode
                and code[offset + 1 :] == SSTORE_ZERO_STOP
            ):
                return ()
            return None

        try:
            candidates = decode_operand(code, offset)
        except FixtureError:
            return None

        for operand, next_offset in candidates:
            operands = decode_operands(next_offset, remaining - 1)
            if operands is not None:
                return (operand, *operands)
        return None

    operands = decode_operands(0, instruction.operand_count)
    if operands is None:
        raise FixtureError(
            f"expected {instruction.fixture_name.upper()} after "
            f"{instruction.operand_count} fixture operands, followed by storage in "
            "slot zero and STOP"
        )
    return operands


def storage_zero(account: dict[str, Any] | None) -> int:
    if account is None:
        return 0
    storage = account.get("storage", {})
    for key, value in storage.items():
        if int(key, 16) == 0:
            return int(value, 16)
    return 0


def calldata_program_index(value: str) -> int:
    data = parse_hex_bytes(value)
    if len(data) < 36:
        raise FixtureError("transaction data must contain a selector and one word")
    return int.from_bytes(data[4:36])


def infer_program_base(addresses: list[int], labels: dict[str, Any]) -> int:
    label_indexes = []
    for label_index in labels:
        try:
            label_indexes.append(int(label_index))
        except ValueError:
            continue
    if not label_indexes:
        return min(addresses)

    address_set = set(addresses)
    candidates = {
        address - label_index
        for address in addresses
        for label_index in label_indexes
        if address >= label_index
    }
    return max(
        candidates,
        key=lambda base: (
            sum(
                base + label_index in address_set
                for label_index in label_indexes
            ),
            base in address_set,
            -base,
        ),
    )


def load_instruction_cases(path: Path, fork: str) -> list[InstructionCase]:
    document = json.loads(path.read_text())
    if not isinstance(document, dict) or len(document) != 1:
        raise FixtureError("fixture must contain exactly one test")
    test_name, test = next(iter(document.items()))
    try:
        instruction = INSTRUCTIONS[test_name]
    except KeyError as error:
        supported = ", ".join(sorted(INSTRUCTIONS))
        raise FixtureError(
            f"unsupported instruction fixture {test_name!r}; supported: {supported}"
        ) from error

    labels = test.get("_info", {}).get("labels", {})
    pre = test.get("pre", {})
    transaction = test.get("transaction", {})
    post = test.get("post", {}).get(fork)
    if not isinstance(post, list):
        raise FixtureError(f"fixture has no post cases for fork {fork!r}")

    program_addresses = [
        int(address, 16)
        for address, account in pre.items()
        if address.lower() != transaction.get("to", "").lower()
        and account.get("code", "0x") != "0x"
    ]
    if not program_addresses:
        raise FixtureError("fixture contains no instruction programs")
    program_base = infer_program_base(program_addresses, labels)

    programs: dict[int, tuple[str, tuple[int, ...]]] = {}
    for address, account in pre.items():
        try:
            operands = decode_program(account.get("code", "0x"), instruction)
        except FixtureError:
            continue
        program_index = int(address, 16) - program_base
        programs[program_index] = (address, operands)
    if not programs:
        raise FixtureError(
            f"fixture contains no supported {instruction.fixture_name.upper()} programs"
        )

    data_values = transaction.get("data", [])
    cases: list[InstructionCase] = []
    for post_case in post:
        indexes = post_case.get("indexes", {})
        data_index = indexes.get("data")
        if (
            not isinstance(data_index, int)
            or data_index < 0
            or data_index >= len(data_values)
        ):
            raise FixtureError("post case has an invalid transaction data index")
        program_index = calldata_program_index(data_values[data_index])
        if program_index not in programs:
            continue

        address, operands = programs[program_index]
        post_state = post_case.get("state", {})
        account = post_state.get(address)
        label = labels.get(str(program_index), f"case_{program_index}")
        cases.append(
            InstructionCase(
                instruction=instruction,
                name=label,
                operands=operands,
                expected=storage_zero(account),
            )
        )
    if not cases:
        raise FixtureError(
            f"fixture selects no supported {instruction.fixture_name.upper()} programs"
        )
    return cases


def render_rocq(
    fixtures: list[Path],
    fork: str,
    cases: list[InstructionCase],
) -> str:
    fixture_names = ", ".join(path.name for path in fixtures)
    lines = [
        "Require Import simulate.RocqOfRust.\n",
    ]
    for instruction in INSTRUCTIONS.values():
        lines.append(
            "Require Import revm.revm_interpreter.instructions.simulate."
            f"{instruction.simulation_module}.\n"
        )
    lines.extend([
        "Require Import revm.revm_interpreter.links.interpreter.\n",
        "Require Import revm.revm_interpreter.tests.interpreter.\n",
        "Require Import revm.revm_interpreter.tests.interpreter_types.\n",
        "Require Import ruint.links.lib.\n",
        "\n",
        f"(** Generated from {fixture_names} in the pinned ethereum/tests "
        f"submodule, fork {fork}. *)\n",
    ])
    for case in cases:
        stack_values = ";\n".join(
            f"    {{| Uint.value := {operand} |}}"
            for operand in reversed(case.operands)
        )
        instruction_arguments = (
            "InterpreterTypes.I interpreter"
            if case.instruction.requires_interpreter_types
            else "interpreter"
        )
        lines.extend(
            [
                f"(** {case.instruction.fixture_name}: {case.name} *)\n",
                "Goal\n",
                "  let stack := {| Stack.value := [\n",
                f"{stack_values}\n",
                "  ] |} in\n",
                "  let interpreter := make_interpreter stack in\n",
                f"  let result := {case.instruction.rocq_name} "
                f"{instruction_arguments} in\n",
                "  result.(Interpreter.stack).(Stack.value) =\n",
                f"    [{{| Uint.value := {case.expected} |}}].\n",
                "Proof.\n",
                "  timeout 5 vm_compute.\n",
                "  reflexivity.\n",
                "Qed.\n",
                "\n",
            ]
        )
    return "".join(lines)


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


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Compile official Ethereum instruction vectors against Rocq REVM"
    )
    parser.add_argument(
        "--fixture",
        action="append",
        type=Path,
        help="instruction fixture to run (default: all supported instructions)",
    )
    parser.add_argument("--fork", default="Cancun")
    parser.add_argument("--emit", type=Path, help="write the generated Rocq source here")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    try:
        fixtures = (
            [path.resolve() for path in args.fixture]
            if args.fixture
            else [
                instruction.fixture_root / f"{name}.json"
                for name, instruction in INSTRUCTIONS.items()
            ]
        )
        for fixture in fixtures:
            if not fixture.is_file():
                raise FixtureError(f"missing REVM fixture: {fixture}; set REVM_FIXTURE_ROOT to the pinned GeneralStateTests directory")
        cases = [
            case
            for fixture in fixtures
            for case in load_instruction_cases(fixture, args.fork)
        ]
        source = render_rocq(fixtures, args.fork, cases)

        if args.emit:
            args.emit.write_text(source)
            generated_path = args.emit.resolve()
            result = run_coqc(generated_path)
        else:
            with tempfile.TemporaryDirectory(prefix="rocq-revm-fixture-") as directory:
                generated_path = Path(directory) / "FixtureTest.v"
                generated_path.write_text(source)
                result = run_coqc(generated_path)

        if result.returncode != 0:
            print(result.stdout, file=sys.stderr, end="")
            return result.returncode
        fixture_names = ", ".join(path.name for path in fixtures)
        print(f"checked {len(cases)} Rocq REVM cases from {fixture_names}")
        return 0
    except (FixtureError, OSError, ValueError, json.JSONDecodeError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
