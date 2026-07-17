""""
Run the snapshot tests for the project by translating all the example files.

Note that we only generate the output files. We do not check them, this can be
done using the `git diff` command.
"""

import os
import subprocess
import sys
import multiprocessing as mp
import shlex


test_folder = "examples"

# For each file recursively in the test folder
rs_files = []
for root, _dirs, files in os.walk(test_folder):
    rs_files += [
        os.path.join(root, file) for file in files if os.path.splitext(file)[1] == ".rs"
    ]


def compile_with_option(file: str, output_path: str, is_axiomatized: bool):
    base = os.path.splitext(file)[0]
    error_path = os.path.join(output_path, base + ".err")
    os.makedirs(os.path.dirname(error_path), exist_ok=True)

    # Translate the file, and save the error output if any
    command = [
        os.environ.get("CARGO", "cargo"),
        "run",
        "--quiet",
        "--bin",
        "rocq-of-rust",
        "--",
        "translate",
        "--path",
        file,
    ]
    if is_axiomatized:
        command.append("--axiomatize")
    command += ["--output-path", output_path]
    print(
        " ".join(shlex.quote(arg) for arg in command)
        + " 2> "
        + shlex.quote(error_path)
    )

    try:
        with open(error_path, "w") as error_file:
            subprocess.run(command, check=True, stderr=error_file)
    except subprocess.CalledProcessError as e:
        print(f"Error occurred: {e}")
        sys.exit(1)
    except KeyboardInterrupt:
        print("Ctrl-C pressed, interrupting the script.")
        sys.exit(1)


def compile(index, file):
    print()
    print(f"Translating file {index + 1}/{len(rs_files)}: {file}")
    compile_with_option(file, "RocqOfRust/examples/default/", False)
    compile_with_option(file, "RocqOfRust/examples/axiomatized/", True)


if __name__ == "__main__":
    if os.environ.get("RUN_TESTS_SINGLE_PROCESS"):
        for index, file in enumerate(rs_files):
            compile(index, file)
    else:
        # run in parallel
        with mp.Pool() as pool:
            pool.starmap(compile, enumerate(rs_files))
