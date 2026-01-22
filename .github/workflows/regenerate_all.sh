#!/bin/bash

set -e

echo "=== Translating Rust examples ==="
python run_tests.py

echo "=== Translating the alloc library ==="
cd third-party/rust/library/alloc
cp ../../../../rust-toolchain ./
cargo build
touch src/lib.rs
cargo rocq-of-rust
rsync -rcv src/ ../../../../RocqOfRust/alloc/ --include='*/' --include='*.v' --include='*.rs' --exclude='*'
cd ../../../..

echo "=== Translating the core library ==="
cd third-party/rust/library/core
cp ../../../../rust-toolchain ./
cargo build
touch src/lib.rs
export RUST_MIN_STACK=800000000
cargo rocq-of-rust
sed -i 's/Module Impl_core_default_Default_where_core_default_Default_T_for_array_expr_T./(* Module Impl_core_default_Default_where_core_default_Default_T_for_array_expr_T./' src/array/mod.v
sed -i 's/End Impl_core_default_Default_where_core_default_Default_T_for_array_expr_T./End Impl_core_default_Default_where_core_default_Default_T_for_array_expr_T. *)/' src/array/mod.v
rsync -rcv src/ ../../../../RocqOfRust/core/ --include='*/' --include='*.v' --include='*.rs' --exclude='*'
cd ../../../..

echo "=== Translating Revm ==="
cd third-party/revm
cp ../../rust-toolchain ./
cd crates

echo "  - bytecode"
cd bytecode
cargo rocq-of-rust
touch src/lib.rs
cargo rocq-of-rust --with-json
rsync -rcv src/ ../../../../RocqOfRust/revm/revm_bytecode/ --include='*/' --include='*.v' --include='*.rs' --include='*.json' --exclude='*'
cd ..

echo "  - context/interface"
cd context/interface
cargo rocq-of-rust
touch src/lib.rs
cargo rocq-of-rust --with-json
rsync -rcv src/ ../../../../../RocqOfRust/revm/revm_context_interface/ --include='*/' --include='*.v' --include='*.rs' --include='*.json' --exclude='*'
cd ../..

echo "  - interpreter"
cd interpreter
cargo rocq-of-rust
touch src/lib.rs
cargo rocq-of-rust --with-json
rsync -rcv src/ ../../../../RocqOfRust/revm/revm_interpreter/ --include='*/' --include='*.v' --include='*.rs' --include='*.json' --exclude='*'
cd ..

echo "  - precompile"
cd precompile
cargo rocq-of-rust
touch src/lib.rs
cargo rocq-of-rust --with-json
rsync -rcv src/ ../../../../RocqOfRust/revm/revm_precompile/ --include='*/' --include='*.v' --include='*.rs' --include='*.json' --exclude='*'
cd ..

echo "  - primitives"
cd primitives
cargo rocq-of-rust
touch src/lib.rs
cargo rocq-of-rust --with-json
rsync -rcv src/ ../../../../RocqOfRust/revm/revm_primitives/ --include='*/' --include='*.v' --include='*.rs' --include='*.json' --exclude='*'
cd ..

echo "  - specification"
cd specification
cargo rocq-of-rust
touch src/lib.rs
cargo rocq-of-rust --with-json
rsync -rcv src/ ../../../../RocqOfRust/revm/revm_specification/ --include='*/' --include='*.v' --include='*.rs' --include='*.json' --exclude='*'
cd ..

cd ../../..

echo "=== Translating ruint ==="
cd third-party/uint
cp ../../rust-toolchain ./
cargo rocq-of-rust
touch src/lib.rs
cargo rocq-of-rust
rsync -rcv src/ ../../RocqOfRust/ruint/ --include='*/' --include='*.v' --include='*.rs' --exclude='*'
cd ../..

echo "=== Translating alloy-core ==="
cd third-party/alloy-rs-core/crates/primitives
cp ../../../../rust-toolchain ./
cargo rocq-of-rust
touch src/lib.rs
cargo rocq-of-rust
rsync -rcv src/ ../../../../RocqOfRust/alloy_primitives/ --include='*/' --include='*.v' --include='*.rs' --exclude='*'
cd ../../../..

echo "=== Translating bytes ==="
cd third-party/bytes
cp ../../rust-toolchain ./
grep -q workspace Cargo.toml || echo '[workspace]' >> Cargo.toml
cargo rocq-of-rust
touch src/lib.rs
cargo rocq-of-rust
rsync -rcv src/ ../../RocqOfRust/bytes/ --include='*/' --include='*.v' --include='*.rs' --exclude='*'
cd ../..

echo "=== Translating Move Sui ==="
cd third-party/move-sui
cp ../../rust-toolchain ./
cd crates

echo "  - move-abstract-stack"
cd move-abstract-stack
cargo rocq-of-rust
touch src/lib.rs
cargo rocq-of-rust
rsync -rcv src/ ../../../../RocqOfRust/move_sui/translations/move_abstract_stack/ --include='*/' --include='*.v' --include='*.rs' --exclude='*'
cd ..

echo "  - move-binary-format"
cd move-binary-format
cargo rocq-of-rust
touch src/lib.rs
cargo rocq-of-rust
rsync -rcv src/ ../../../../RocqOfRust/move_sui/translations/move_binary_format/ --include='*/' --include='*.v' --include='*.rs' --exclude='*'
cd ..

echo "  - move-bytecode-verifier"
cd move-bytecode-verifier
cargo rocq-of-rust
touch src/lib.rs
cargo rocq-of-rust
rsync -rcv src/ ../../../../RocqOfRust/move_sui/translations/move_bytecode_verifier/ --include='*/' --include='*.v' --include='*.rs' --exclude='*'
cd ..

echo "  - move-bytecode-verifier-meter"
cd move-bytecode-verifier-meter
cargo rocq-of-rust
touch src/lib.rs
cargo rocq-of-rust
rsync -rcv src/ ../../../../RocqOfRust/move_sui/translations/move_bytecode_verifier_meter/ --include='*/' --include='*.v' --include='*.rs' --exclude='*'
cd ..

echo "  - move-core-types"
cd move-core-types
cargo rocq-of-rust
touch src/lib.rs
cargo rocq-of-rust
rsync -rcv src/ ../../../../RocqOfRust/move_sui/translations/move_core_types/ --include='*/' --include='*.v' --include='*.rs' --exclude='*'
cd ..

cd ../../..

echo "=== Translating the Token program ==="
cd third-party/solana-program-token
cp ../../rust-toolchain ./

echo "  - pinocchio/program"
cd pinocchio/program
cargo rocq-of-rust
touch src/lib.rs
cargo rocq-of-rust
rsync -rcv ./src/ ../../../../RocqOfRust/solana_program_token/pinocchio --include='*/' --include='*.v' --include='*.rs' --exclude='*'
cd ../..

echo "  - program"
cd program
cargo rocq-of-rust
touch src/lib.rs
cargo rocq-of-rust
rsync -rcv ./src/ ../../../RocqOfRust/solana_program_token/program --include='*/' --include='*.v' --include='*.rs' --exclude='*'
cd ..

echo "  - interface"
cd interface
cargo rocq-of-rust
touch src/lib.rs
cargo rocq-of-rust
rsync -rcv ./src/ ../../../RocqOfRust/solana_program_token/interface --include='*/' --include='*.v' --include='*.rs' --exclude='*'
cd ..

cd ../..

echo "=== Translating the Solana SDK ==="
cd third-party/anza-xyz-solana-sdk
cp ../../rust-toolchain ./

echo "  - account-info"
cd account-info
cargo rocq-of-rust
touch src/lib.rs
cargo rocq-of-rust
rsync -rcv ./src/ ../../../RocqOfRust/anza_xyz_solana_sdk/account_info --include='*/' --include='*.v' --include='*.rs' --exclude='*'
cd ..

echo "  - address"
cd address
cargo rocq-of-rust
touch src/lib.rs
cargo rocq-of-rust
rsync -rcv ./src/ ../../../RocqOfRust/anza_xyz_solana_sdk/address --include='*/' --include='*.v' --include='*.rs' --exclude='*'
cd ..

echo "  - program-error"
cd program-error
cargo rocq-of-rust
touch src/lib.rs
cargo rocq-of-rust
rsync -rcv ./src/ ../../../RocqOfRust/anza_xyz_solana_sdk/program_error --include='*/' --include='*.v' --include='*.rs' --exclude='*'
cd ..

echo "  - program-option"
cd program-option
cargo rocq-of-rust
touch src/lib.rs
cargo rocq-of-rust
rsync -rcv ./src/ ../../../RocqOfRust/anza_xyz_solana_sdk/program_option --include='*/' --include='*.v' --include='*.rs' --exclude='*'
cd ..

echo "  - program-pack"
cd program-pack
cargo rocq-of-rust
touch src/lib.rs
cargo rocq-of-rust
rsync -rcv ./src/ ../../../RocqOfRust/anza_xyz_solana_sdk/program_pack --include='*/' --include='*.v' --include='*.rs' --exclude='*'
cd ..

echo "  - pubkey"
cd pubkey
cargo rocq-of-rust
touch src/lib.rs
cargo rocq-of-rust
rsync -rcv ./src/ ../../../RocqOfRust/anza_xyz_solana_sdk/pubkey --include='*/' --include='*.v' --include='*.rs' --exclude='*'
cd ..

cd ../..

echo "=== Generate Rocq files from Python ==="
cd RocqOfRust
make generate
cd ..

echo "=== Generate Rocq files from Jinja ==="
cd RocqOfRust
make jinja
cd ..

echo "=== All translations complete ==="
