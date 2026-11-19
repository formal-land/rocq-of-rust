#!/bin/bash -x

cd ../ink

# Translate the Ink libraries
time cargo rocq-of-rust --axiomatize
# Removing these files as they are too long
rm ink_codegen.v ink_ir.v ink_metadata.v
mv *.v ../RocqOfRust/ink/

# Translate the ERC20 example
cd integration-tests/erc20
time cargo rocq-of-rust
mv erc20.v ../../../RocqOfRust/ink/

# Apply manual changes to the translations
cd ../../../RocqOfRust/ink/
python update_after_translation.py
