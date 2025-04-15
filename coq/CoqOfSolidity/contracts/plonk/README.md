# Readme

Here are the commands to translate the PlonkVerifier contract to Rocq. Assuming you are in the folder `coq/` of this project, run:

```sh
../build/solc/solc --ir-optimized-ast-json --optimize --yul-optimizations hg CoqOfSolidity/contracts/plonk/PlonkVerifier.sol | head -2 | tail -1 | jq 'walk(if type == "object" then del(.nativeSrc, .src, .type) else . end)' > CoqOfSolidity/contracts/plonk/PlonkVerifier.json
python scripts/shallow_embed.py CoqOfSolidity/contracts/plonk/PlonkVerifier.json > CoqOfSolidity/contracts/plonk/PlonkVerifier.v
```

This will generate the file `PlonkVerifier.v` that is already saved in the repository.

To compile all the Rocq files you can run:

```sh
make
```

from the folder `coq/CoqOfSolidity/`.
