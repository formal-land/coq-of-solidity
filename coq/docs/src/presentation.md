# Presentation

Here is a 🏎️&nbsp;quick presentation, in simple words, of what `coq-of-solidity` does.

> With `coq-of-solidity` you make sure that the money stored on your Solidity smart contract cannot be stolen. 🛡️

Every month, millions of dollars&nbsp;💰 are stolen from smart contracts. This is because a single mistake in the code, even if this is just one line, lets an attacker withdraw all the money and disappear with it!

Audits are mandatory, but this is a human&nbsp;🧠 verifying the code, and mistakes are made.

> 🚨&nbsp;Even if major smart contracts have all been audited, they are still regularly hacked.

With `coq-of-solidity`, the computer checks that the reasoning of the auditor is correct: this is like a spell checker for auditors.

As a result, you can truly be sure that no attack scenario has been forgotten and that your smart contract is truly secure&nbsp;✅.

In addition, when you update the code of your smart contract, you can replay the reasoning for free to make sure your smart contract is still secure on the old part&nbsp;😎 . This _saves on auditing costs_.

## Why us?

Verifying reasoning about code is called 🔎&nbsp;_formal verification_. This is a complex technique&nbsp;🧪 and very few companies have developed a tool to do this for Solidity. In addition, `coq-of-solidity` is the only one with [Clear](https://github.com/NethermindEth/Clear) that can express any possible reasoning/property on your code. This is thanks to the use of an 🐓&nbsp;interactive theorem prover on the backend.

At [🌲&nbsp;Formal Land](https://formal.land/), where we developed `coq-of-solidity`, we are one of the leading teams applying formal verification to large-scale programs. We have developed two other formal verification tools, with [coq-of-rust](https://github.com/formal-land/coq-of-rust) for 🦀&nbsp;Rust and [coq-of-ocaml](https://github.com/formal-land/coq-of-ocaml) for 🐫&nbsp;OCaml. Read more about what we do on our [📖&nbsp;blog](https://formal.land/blog).

## How much? 💸

For a large smart contract (5,000 lines of Solidity), consider a price of **$50,000** for a formal verification of a _model_ of the code, and **$100,000** for a verification at the level of the _source code_ (more precise). So, this is competitive with traditional audits.

[💌&nbsp;Contact us](mailto:&#099;&#111;&#110;&#116;&#097;&#099;&#116;&#064;formal&#046;&#108;&#097;&#110;&#100;) for an evaluation!
