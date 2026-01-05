#!/bin/sh

# The light version of a Makefile for testing, as `rocqdep` takes several minutes to run on the
# whole project.

# Display the commands being run.
set -x

coqc -R . RocqOfSolidity -impredicative-set RocqOfSolidity.v
coqc -R . RocqOfSolidity -impredicative-set test/libsolidity/semanticTests/various/erc20/ERC20.v
coqc -R . RocqOfSolidity -impredicative-set simulations/RocqOfSolidity.v
coqc -R . RocqOfSolidity -impredicative-set test/libsolidity/semanticTests/various/erc20/GeneratedTest.v
coqc -R . RocqOfSolidity -impredicative-set simulations/erc20.v
coqc -R . RocqOfSolidity -impredicative-set test/libsolidity/semanticTests/various/erc20/ERC20_functional.v
coqc -R . RocqOfSolidity -impredicative-set proofs/ERC20_functional.v
coqc -R . RocqOfSolidity -impredicative-set test/libsolidity/semanticTests/various/erc20/ERC20_functional_proof.v
