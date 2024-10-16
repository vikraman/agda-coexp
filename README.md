# agda-coexp

[![ci](https://github.com/vikraman/agda-coexp/actions/workflows/ci.yml/badge.svg)](https://github.com/vikraman/agda-coexp)

This is a formalisation of the calculi in The Duality of Abstraction.

The source is automatically checked and hosted at: https://vikraman.github.io/agda-coexp/

## Comments

- The syntax is formalised in intrinsically well-scoped, well-typed style, or as second-order abstract syntax.
- The interpretation is given directly into Agda's Set, extended with a continuation monad, assuming a response object R.
- Function extensionality (with a computation rule) is required for the proofs, which is obtained by postulating an interval object.
- Agda's rewriting mechanism is used to automate the use of coherence lemmas.
- Some equations and evaluation contexts are skipped, because they are too tedious to formalise.
