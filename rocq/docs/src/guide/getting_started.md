# Getting Started

Here we give you the instructions to get started to translate Solidity smart contracts to Rocq.

## Translate Solidity to Rocq

If you have a smart contract named `contract.sol`, generate the JSON of its unoptimized Yul code with the following command:

```
solc --ir-ast-json contract.sol \
  | tail -1 \
  > contract.yul.json
```

assuming you have installed the Solidity compiler `solc`.

Then clone the repository of [rocq-of-solidity](https://github.com/formal-land/rocq-of-solidity):

```
git clone https://github.com/formal-land/rocq-of-solidity.git
cd rocq-of-solidity
```

Then translate it to Rocq with the following command:

```
python rocq/scripts/shallow_embed.py path/to/contract.yul.json \
  > shallow.v
```

The resulting file `shallow.v` contains the Rocq code of the smart contract. Generally the first part is the deployment code (constructor), and then comes the code for the entrypoints of the smart contract.

## Compile the generated Rocq code

Assuming you have a working installation of the [opam]() package manager that we use for Rocq, from the root of the `rocq-of-solidity` repository, run the following command to install the `RocqOfSolidity` library:

```
opam install --deps-only rocq/RocqOfSolidity/rocq-of-solidity.opam
```

Then go to the directory with the Rocq code:

```
cd rocq/RocqOfSolidity
```

Compile and install the `RocqOfSolidity` library:

```
make -j3
make install
```

You can now compile your generated `shallow.v` file, for example opening it in VSCode with the Rocq extension installed.
