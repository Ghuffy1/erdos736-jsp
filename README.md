# Erdős 736 — a ZFC counterexample to Taylor's conjecture

This repository contains a complete mathematical proof and a Lean 4 formalization of the negative answer to Erdős Problem 736. The corresponding Justin Sun Prize entry is **JSP-000604**.

The construction gives a graph of chromatic number `aleph_1` such that every graph whose finite ordinary subgraphs occur in it has chromatic number at most the continuum. The successor of the continuum supplies the required obstruction.

## Read the proof

- [Mathematical paper](paper/erdos736.pdf), Theorem 1.1 and its complete proof on pages 1–6.
- [Paper source](paper/erdos736.tex).
- [Complete standalone formal proof](Erdos736.lean).
- [Original-statement check](StatementCheck.lean).
- [Statement correspondence](STATEMENT.md).
- [Reproduction instructions](BUILD.md).
- [Authorship, AI assistance, and prior work](ATTRIBUTION.md).

The principal theorem is `Erdos736.erdos_736`. The stronger constructive statement is `Erdos736.full_solution`. The independently written original assertion is discharged by `StatementCheck.original_assertion_false`.

## Contributors

| Author | GitHub account | Contribution credit |
| --- | --- | --- |
| Will Howe | [H0W4RD-dev](https://github.com/H0W4RD-dev) | Equal contributor |
| Grant Huffman | [Ghuffy1](https://github.com/Ghuffy1) | Equal contributor, repository owner and submission lead |
| Jensen Kohlmeyer | [JENW1N](https://github.com/JENW1N) | Equal contributor |
| Liam Kruer | [lkruer](https://github.com/lkruer) | Equal contributor |

Names are ordered alphabetically by surname. The team credits OpenAI ChatGPT/Codex for assistance with the mathematical development, formalization, verification, and exposition. The attribution record describes the inherited mathematical construction and the contribution presented here.

## Reproduce

Install the Lean toolchain manager `elan`, make `lake` available on the command line, and run the following commands from the repository root.

```sh
lake exe cache get
lake build
lake env lean Audit.lean
lake env leanchecker --fresh Erdos736
lake env leanchecker StatementCheck
```

Lean is fixed at `4.34.0`. Mathlib is fixed at `5ed2965256430c3649e86755f9576b54eca72435`. Every transitive dependency is pinned in `lake-manifest.json`. [BUILD.md](BUILD.md) gives the clean-checkout procedure and explains the checks.

## Submission status

This is the authors' submission material for mathematical and formal verification. Official mathematical review, attribution review, priority determination, candidate registration, and award decisions are performed by the prize organizers.

## Licenses

Original formalization, scripts, and repository documentation are offered under the [MIT license](LICENSE). The mathematical paper and its source are offered under [CC BY 4.0](LICENSE-PAPER). Third-party sources retain their original rights. Dependencies are fetched from their upstream repositories.
