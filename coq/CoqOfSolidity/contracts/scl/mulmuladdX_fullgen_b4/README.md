# ⚈ Formal verification of Smoo.th

In this folder is our formal verification project to verify the correctness of the library [Smoo.th](https://smoo.th/). This is still an ongoing work. You can find the code we are verifying on [github.com/get-smooth/crypto-lib/blob/main/src/elliptic/SCL_mulmuladdX_fullgen_b4.sol](https://github.com/get-smooth/crypto-lib/blob/main/src/elliptic/SCL_mulmuladdX_fullgen_b4.sol).

## 📚 Library

The Smoo.th library is an optimized implementation in [Solidity](https://soliditylang.org/) of the [elliptic curve](https://en.wikipedia.org/wiki/Elliptic_curve) operations of addition and scalar multiplication, which are at the basis of most of the authentication algorithms in the blockchain or the Web2 space. The code is carefully optimized by hand using:

- the assembly of Solidity, the [Yul](https://docs.soliditylang.org/en/latest/yul.html) language,
- an algorithm based on the bit decomposition of the scalars.

The [audit report from CryptoExperts](https://github.com/get-smooth/crypto-lib/blob/main/doc/Audits/CRX_smooth_report_2024_07_11_v1.2.pdf) gives a nice overview of the library and how its algorithms work.

When looking exclusively at [SCL_mulmuladdX_fullgen_b4.sol](https://github.com/get-smooth/crypto-lib/blob/main/src/elliptic/SCL_mulmuladdX_fullgen_b4.sol) (there is also [SCL_mulmuladdX_fullgenW.sol](https://github.com/get-smooth/crypto-lib/blob/main/src/elliptic/SCL_mulmuladdX_fullgenW.sol) giving a similar implementation), the library is composed of one main function composed of more than 200 lines of Yul code. We want to show that all this code is equivalent to the basic but unoptimized implementation of the elliptic curve operations (addition and scalar multiplication).

## ✅ Formal verification

Our verification is not complete as of today. We have verified the following:

- The addition operation `ecAddn2` is implemented as in the specification.
- The doubling and negation operation `ecDblNeg` is implemented as in the specification, in an inlined manner.
- The pre-computations of the sums of the possible combinations of points is correct.
- The retrieval of the pre-computed sums from the current bits of the scalars is correct.

We are currently blocked by the complexity of our representation for the library in Coq. We are verifying the Yul code after the optimization pass of the Solidity compiler. This pass adds complexity as many variable names disappear and are replaced by arbitrary locations in the memory. Keeping all the names would simplify keeping the verification effort aligned to the source code and expressing the invariants about data in the loops. So, verifying the code before the optimization passes is the a first improvement that we see. There are probably further improvements we could make, for example, on the reasoning principles of field arithmetic. There are a few dedicated Coq libraries for this problem that we need to investigate.

## 🧭 How

We do our verification by:

1. Translating the code to Coq using `coq-of-solidity`. More precisely, we use our script [coq/scripts/shallow_embed.py](/coq/scripts/shallow_embed.py) to generate a translation as a shallow embedding in Coq. In contrast to a deep embedding, a shallow embedding has a form that is simpler to reason about, as it more directly uses the features of the target language. From this step, we obtain the file [coq/contracts/scl/mulmuladdX_fullgen_b4/shallow.v](/coq/contracts/scl/mulmuladdX_fullgen_b4/shallow.v).
2. Executing the contract step by step in a symbolic manner, to show it equivalent to a simpler and idiomatic Coq definition. This is done in the file [coq/contracts/scl/mulmuladdX_fullgen_b4/run.v](/coq/contracts/scl/mulmuladdX_fullgen_b4/run.v). Note that this is still a work in progress.
3. Showing that the idiomatic Coq version is equivalent to the canonical definition of the elliptic curve operations. This is a work that remains to be done, which will involve reasoning about the two loops implemented in the code, to find the most significant bits of the scalars and to perform the additions and doubling of the points bit by bit.

## 🔄 Reproduce

Assuming you have a working installation of the Coq proof system, you can re-generate and check all of our files by running the following commands. We first assume that you have compiled `coq-of-solidity`, what you can do by applying the instructions to build the solidity compiler from sources given on https://docs.soliditylang.org/en/v0.8.28/installing-solidity.html#building-from-source

Then run in the folder `coq/`:

```sh
scripts/contracts_generate.sh
cd CoqOfSolidity/
make # Compile all the proofs. This may take a few minutes.
```

## 📰 Blog posts

For more information, you can read our associated blog posts:

- [🪁 Enhancements to coq-of-solidity – 1](https://formal.land/blog/2024/10/16/coq-of-solidity-enhanced-version-1)
- [⚈ Verification of the Smoo.th library – 1](https://formal.land/blog/2024/10/21/verification-smooth-library-1)
- [⚈ Verification of the Smoo.th library – 2](https://formal.land/blog/2024/10/28/verification-smooth-library-2)

## 💌 Contact

If you have any additional questions, do not hesitate to reach us at [contact@formal.land](mailto:contact@formal.land)!
