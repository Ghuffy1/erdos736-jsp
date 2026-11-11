# Reproducing the formal proof

## Environment

- Lean toolchain `leanprover/lean4:v4.34.0`, selected by [lean-toolchain](lean-toolchain).
- Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`, selected by [lakefile.toml](lakefile.toml).
- All nine dependency revisions fixed by [lake-manifest.json](lake-manifest.json).
- Git and the Lean toolchain manager `elan` available on the command line.

Use the full commit specified in the submission record when checking a submission. Obtain a clean checkout of that commit before running the following commands. Preserve the committed dependency manifest.

## Build and statement check

```sh
lake --version
lake env lean --version
lake exe cache get
lake build
lake env lean -DautoImplicit=false StatementCheck.lean
lake env lean Audit.lean
```

`lake build` builds the standalone proof, the independent original-statement check, and the audit module. All three are default targets. Each command must exit with status zero. The mathematical target is `Erdos736.erdos_736`, and the expanded statement target is `StatementCheck.original_assertion_false`.

The cache command retrieves compiled upstream dependencies. It does not supply the submitted proof. `Erdos736.lean` and `StatementCheck.lean` are compiled locally from source.

## Axiom audit

[Audit.lean](Audit.lean) includes the following commands.

```lean
#print axioms Erdos736.erdos_736
#print axioms Erdos736.full_solution
#print axioms StatementCheck.original_assertion_false
```

The expected dependency set for each is exactly `propext`, `Classical.choice`, and `Quot.sound`. Run `lake env lean Audit.lean` to obtain the actual report for the selected checkout.

## Kernel replay

After the build, run

```sh
lake env leanchecker --fresh Erdos736
lake env leanchecker StatementCheck
```

The first command performs a fresh replay of the proof module and its imported environment. The second checks the module containing the expanded original assertion. Each command must exit successfully.

## Automated local check

With Python 3.10 or later installed, the standard-library-only checker runs the same build, source, dependency, statement, axiom, and kernel checks and writes a timestamped local report.

```sh
python scripts/verify.py
```

The report records the actual Git commit and source hashes. Output is written under `.verification/` and excluded from version control. This checker requires that each dependency checkout matches the committed manifest. Its dependency inspection reads existing checkouts and does not change them.

## Paper

The delivered paper is [paper/erdos736.pdf](paper/erdos736.pdf). The matching source is [paper/erdos736.tex](paper/erdos736.tex). It can be rebuilt with a standard LaTeX installation and the `amsart`, Latin Modern, `geometry`, `amsmath`, `amssymb`, `amsthm`, `mathtools`, `microtype`, and `hyperref` packages, or with Tectonic. The paper is a self-contained mathematical exposition.
