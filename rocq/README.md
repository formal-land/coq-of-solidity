This is the directory with the Rocq files for the translation from Solidity to Rocq.

## Generate the test files

## Compile the Rocq files

Go to the folder `RocqOfSolidity/` and run:

```sh
make
```

To compile the generated test files you need to use a dedicated command instead of the `Makefile` above, as `rocqdep` is taking too long on this folder (several minutes). Go to the current directory and run:

```sh
python scripts/tests_compile.py
```
