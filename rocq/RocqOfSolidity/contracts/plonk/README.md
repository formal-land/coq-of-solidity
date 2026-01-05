# Readme

Here are the commands to translate the PlonkVerifier contract to Rocq. Assuming you are in the folder `rocq/` of this project, run:

```sh
../build/solc/solc --ir-optimized-ast-json --optimize --yul-optimizations hg RocqOfSolidity/contracts/plonk/PlonkVerifier.sol | head -2 | tail -1 | jq 'walk(if type == "object" then del(.nativeSrc, .src, .type) else . end)' > RocqOfSolidity/contracts/plonk/PlonkVerifier.json
python scripts/shallow_embed.py RocqOfSolidity/contracts/plonk/PlonkVerifier.json > RocqOfSolidity/contracts/plonk/PlonkVerifier.v
```

This will generate the file `PlonkVerifier.v` that is already saved in the repository.

To compile all the Rocq files you can run:

```sh
make
```

from the folder `rocq/RocqOfSolidity/`.
