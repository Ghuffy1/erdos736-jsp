# Verification of the selected proof commit

This evidence refers to proof commit `9a07b93bc7466a489650c3951e0642689c5d8bc5`. The evidence is stored in a later commit. The selected proof and statement files retain their checked contents.

## Completed checks

- The committed standalone proof and independent original assertion build with Lean 4.34.0.
- The nine dependency revisions match `lake-manifest.json` and have clean source worktrees.
- The main theorem, constructive theorem, and original-statement theorem have exactly the reported standard axiom dependencies.
- Fresh kernel replay of `Erdos736` and replay of `StatementCheck` exit successfully.
- A separate clean Git checkout of the selected proof revision builds the three default targets and reproduces the axiom report.
- The packaged paper is byte-identical to the seven-page paper reviewed before repository preparation.

[Machine-readable check results](report.json), [clean-checkout results](clean-checkout.json), [source preservation](source-preservation.json), and [complete selected-commit file hashes](proof-commit-files.json) identify the exact checked inputs.

The command output is retained in `lean-version.txt`, `build.txt`, `statement.txt`, `axioms.txt`, `kernel-replay.txt`, `statement-kernel-replay.txt`, `clean-cache.txt`, `clean-build.txt`, and `clean-axioms.txt`. A command may succeed with empty output. Its exit status is recorded in the corresponding report.

## Statement and mathematical review

[STATEMENT.md](../STATEMENT.md) records the correspondence to the original problem and coverage of the construction. [ATTRIBUTION.md](../ATTRIBUTION.md) records the mathematical antecedents and contribution scope. The main theorem has no additional mathematical hypothesis, and the proof source contains no admitted step or newly declared mathematical axiom.

## Verification environment and scope

Execution used a Windows x86-64 installation of the pinned Lean toolchain. The clean checkout reused checked upstream dependency sources and their compiled cache, with a successful `lake exe cache get`. Its own proof targets were rebuilt from source. The fresh kernel check supplies an additional replay of the proof environment.

The included GitHub Actions workflow is prepared for subsequent hosted execution. These records describe actual local execution. External mathematical review, an independent checker implementation, public priority evidence, and prize-organizer acceptance remain separate review matters.

## Final pre-submission verification

The complete checks were repeated successfully in another clean checkout of the same proof commit before publication. [Final results](final-report.json) record the actual completion time and source hashes. [Package checks](final-package-check.json) cover metadata, statement links, the paper, attribution, catalog scope, and the privacy scan across the entire prepared history. The command output is retained in the corresponding `final-*.txt` files.
