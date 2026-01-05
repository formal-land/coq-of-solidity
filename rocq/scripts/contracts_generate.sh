#!/bin/sh
set -x #echo on

# Generate various files needed for the verification of the contracts.
#
# We assume that `solc` has been compiled from the source in the `build/` directory at the root of
# the repository. This script should be launched from the `rocq/` directory.

# erc20
../build/solc/solc --ir-rocq --optimize RocqOfSolidity/contracts/erc20/contract.sol \
  > RocqOfSolidity/contracts/erc20/contract.v
../build/solc/solc --ir-optimized --optimize RocqOfSolidity/contracts/erc20/contract.sol \
  > RocqOfSolidity/contracts/erc20/contract.yul
../build/solc/solc --ir-optimized-ast-json --optimize RocqOfSolidity/contracts/erc20/contract.sol \
  | tail -1 \
  | jq 'walk(if type == "object" then del(.nativeSrc, .src, .type) else . end)' \
  > RocqOfSolidity/contracts/erc20/contract.json
python scripts/shallow_embed.py RocqOfSolidity/contracts/erc20/contract.json \
  > RocqOfSolidity/contracts/erc20/shallow.v
# python scripts/shallow_embed_proof.py RocqOfSolidity/contracts/erc20/contract.json \
#   > RocqOfSolidity/contracts/erc20/shallow_proof.v

# SCL_mulmuladdX_fullgen_b4
# We only use the optimization to group the functions at top-level, as we do not handle them otherwise.
# This is the optimization with the flag "hg".
../build/solc/solc --ir-rocq --optimize --yul-optimizations hg RocqOfSolidity/contracts/scl/mulmuladdX_fullgen_b4/contract.sol \
  > RocqOfSolidity/contracts/scl/mulmuladdX_fullgen_b4/contract.v
# ../build/solc/solc --ir RocqOfSolidity/contracts/scl/mulmuladdX_fullgen_b4/contract.sol \
#   > RocqOfSolidity/contracts/scl/mulmuladdX_fullgen_b4/contract.yul
# ../build/solc/solc --ir-optimized-ast-json --optimize --yul-optimizations hg RocqOfSolidity/contracts/scl/mulmuladdX_fullgen_b4/contract.sol \
#   | tail -1 \
#   | jq 'walk(if type == "object" then del(.nativeSrc, .src, .type) else . end)' \
#   > RocqOfSolidity/contracts/scl/mulmuladdX_fullgen_b4/contract.json
# ../build/solc/solc --ir-ast-json RocqOfSolidity/contracts/scl/mulmuladdX_fullgen_b4/contract.sol \
#   | tail -1 \
#   | jq 'walk(if type == "object" then del(.nativeSrc, .src, .type) else . end)' \
#   > RocqOfSolidity/contracts/scl/mulmuladdX_fullgen_b4/contract.json
python scripts/shallow_embed.py RocqOfSolidity/contracts/scl/mulmuladdX_fullgen_b4/contract.json \
  > RocqOfSolidity/contracts/scl/mulmuladdX_fullgen_b4/shallow.v
# python scripts/shallow_embed_proof.py RocqOfSolidity/contracts/scl/mulmuladdX_fullgen_b4/contract.json \
#   > RocqOfSolidity/contracts/scl/mulmuladdX_fullgen_b4/shallow_proof.v

# tutorial
../build/solc/solc --ir-rocq --optimize RocqOfSolidity/contracts/tutorial/contract.sol \
  > RocqOfSolidity/contracts/tutorial/contract.v
../build/solc/solc --ir RocqOfSolidity/contracts/tutorial/contract.sol \
  > RocqOfSolidity/contracts/tutorial/contract.yul
../build/solc/solc --ir-ast-json RocqOfSolidity/contracts/tutorial/contract.sol \
  | tail -1 \
  | jq 'walk(if type == "object" then del(.nativeSrc, .src, .type) else . end)' \
  > RocqOfSolidity/contracts/tutorial/contract.json
python scripts/shallow_embed.py RocqOfSolidity/contracts/tutorial/contract.json \
  > RocqOfSolidity/contracts/tutorial/shallow.v
