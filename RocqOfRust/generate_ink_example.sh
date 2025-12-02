#!/bin/bash -x

CONFIG_FILE="$PWD/../rocq-of-rust-config.json"
cd ../ink

# Translate the Ink libraries
# We do a "touch" to make sure that the compilation is restarted
touch crates/*/src/lib.rs
time cargo rocq-of-rust --axiomatize --configuration-file $CONFIG_FILE
# Removing these files as they are too long
rm ink_codegen.v ink_ir.v ink_metadata.v
mv *.v ../RocqOfRust/ink/

# Translate the ERC20 example
cd integration-tests/erc20
touch lib.rs
time cargo rocq-of-rust --configuration-file $CONFIG_FILE
mv erc20.v ../../../RocqOfRust/ink/

# Apply manual changes to the translations
cd ../../../RocqOfRust/ink/
python update_after_translation.py
