"""Check the committed proof, statement correspondence, and axiom dependencies."""

from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess


ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / ".verification"
OUTPUT.mkdir(exist_ok=True)
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
TARGETS = [
    "Erdos736.erdos_736",
    "Erdos736.full_solution",
    "StatementCheck.original_assertion_false",
]


def git_output(*arguments):
    return subprocess.check_output(
        ["git", *arguments], cwd=ROOT, text=True, encoding="utf-8"
    ).strip()


def run_check(name, arguments):
    print(f"Checking {name}", flush=True)
    result = subprocess.run(
        arguments,
        cwd=ROOT,
        text=True,
        encoding="utf-8",
        errors="replace",
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )
    (OUTPUT / f"{name}.log").write_text(
        result.stdout, encoding="utf-8", newline="\n"
    )
    print(f"{name} exited {result.returncode}", flush=True)
    if result.returncode != 0:
        raise SystemExit(result.stdout)
    return result.stdout


def main():
    lake = shutil.which("lake")
    if lake is None:
        raise SystemExit("Install elan and make lake available on PATH.")
    revision = git_output("rev-parse", "HEAD")
    if git_output("status", "--porcelain", "--untracked-files=normal"):
        raise SystemExit("Check a clean committed checkout.")

    source_hashes = {}
    for name in ["Erdos736.lean", "StatementCheck.lean", "Audit.lean"]:
        data = (ROOT / name).read_bytes()
        text = data.decode("utf-8")
        forbidden = re.findall(r"\b(?:sorry|admit|axiom|native_decide|unsafe)\b", text)
        if forbidden:
            raise SystemExit(f"Review forbidden proof token in {name}: {forbidden}")
        source_hashes[name] = hashlib.sha256(data).hexdigest()

    toolchain = (ROOT / "lean-toolchain").read_text().strip()
    if toolchain != "leanprover/lean4:v4.34.0":
        raise SystemExit("Unexpected Lean toolchain.")
    version = run_check("lean-version", [lake, "env", "lean", "--version"])
    if "version 4.34.0," not in version:
        raise SystemExit("The installed Lean version differs from the pin.")

    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    dependencies = []
    for package in manifest["packages"]:
        directory = ROOT / ".lake" / "packages" / package["name"]
        actual = subprocess.check_output(
            ["git", "-C", str(directory), "rev-parse", "HEAD"], text=True
        ).strip()
        dirty = subprocess.check_output(
            ["git", "-C", str(directory), "status", "--porcelain"], text=True
        ).strip()
        if actual != package["rev"] or dirty:
            raise SystemExit(f"Dependency differs from its pin: {package['name']}")
        dependencies.append({"name": package["name"], "commit": actual})

    run_check("build", [lake, "build"])
    run_check("statement", [lake, "env", "lean", "-DautoImplicit=false", "StatementCheck.lean"])
    audit = run_check("axioms", [lake, "env", "lean", "Audit.lean"])
    reports = dict(re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", audit))
    for target in TARGETS:
        if target not in reports:
            raise SystemExit(f"Missing axiom report for {target}")
        axioms = {name.strip() for name in reports[target].split(",") if name.strip()}
        if axioms != ALLOWED_AXIOMS:
            raise SystemExit(f"Unexpected axiom set for {target}: {sorted(axioms)}")

    run_check("kernel-replay", [lake, "env", "leanchecker", "--fresh", "Erdos736"])
    run_check("statement-kernel-replay", [lake, "env", "leanchecker", "StatementCheck"])
    if git_output("status", "--porcelain", "--untracked-files=normal"):
        raise SystemExit("A tracked file changed during verification.")

    report = {
        "checked_at_utc": datetime.now(timezone.utc).isoformat(),
        "checked_commit": revision,
        "toolchain": toolchain,
        "lean_version": version.strip(),
        "source_sha256": source_hashes,
        "dependencies": dependencies,
        "targets": TARGETS,
        "axioms": {target: reports[target].split(", ") for target in TARGETS},
        "source_scan": "passed",
        "build": "passed",
        "statement_check": "passed",
        "axiom_audit": "passed",
        "fresh_kernel_replay": "passed",
        "statement_kernel_replay": "passed",
        "dependency_mode": "pinned dependency checkouts and available upstream build cache",
        "external_prize_review": "pending",
    }
    (OUTPUT / "report.json").write_text(
        json.dumps(report, indent=2) + "\n", encoding="utf-8", newline="\n"
    )
    print(f"All checks passed for {revision}", flush=True)


if __name__ == "__main__":
    main()
