# Getting Started

Here we give you the instructions to get started to translate Solidity smart contracts to Coq.

## Translate Solidity to Coq

If you have a smart contract named `contract.sol`, generate the JSON of its unoptimized Yul code with the following command:

```
solc --ir-ast-json contract.sol \
  | tail -1 \
  > contract.yul.json
```

assuming you have installed the Solidity compiler `solc`.

Then clone the repository of [coq-of-solidity](https://github.com/formal-land/coq-of-solidity):

```
git clone --recursive https://github.com/formal-land/coq-of-solidity.git
cd coq-of-solidity
```

Then translate it to Coq with the following command:

```
python coq/scripts/shallow_embed.py path/to/contract.yul.json \
  > shallow.v
```

The resulting file `shallow.v` contains the Coq code of the smart contract. Generally the first part is the deployment code (constructor), and then comes the code for the entrypoints of the smart contract.

## Compile the generated Coq code

Assuming you have a working installation of the [opam]() package manager that we use for Coq, from the root of the `coq-of-solidity` repository, run the following command to install the `CoqOfSolidity` library:

```
opam install --deps-only coq/CoqOfSolidity/coq-of-solidity.opam
```

Then go to the directory with the Coq code:

```
cd coq
```

Install the `coq-evm` dependency including the definition of cryptographic primitives such as Keccak256:

```
third-party/coq-evm
./configure
make
make install
cd ../..
```

Compile and install the `CoqOfSolidity` library:

```
cd CoqOfSolidity
make
make install
cd ..
```

You can now compile your generated `shallow.v` file, for example opening it in VSCode with the Coq extension installed.
