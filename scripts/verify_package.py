#!/usr/bin/env python3
"""Check the source-only package against the accepted snapshots, without Lean."""

from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import re
import sys
import tomllib


SUPPORT_FILES = {
    "Challenge.lean", "ChallengeDeps.lean", "Solution.lean", "WorkspaceTest.lean",
    "config.json", "holes.json", "lakefile.toml", "lean-toolchain", "README.md",
    "lake-manifest.json",
}
ROOT_FILES = {
    ".gitignore", "README.md", "PROVENANCE.md", "LICENSE", "NOTICE", "verification.json",
    "third-party/README.md", "third-party/lean-eval-LICENSE",
    "third-party/lean-eval-SECURITY.md", "scripts/verify_package.py",
    "accepted-results.json",
}
EXPECTED_PROBLEMS = {"coc_strong_normalization", "rcf_quantifier_elimination"}


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def digest(workspace: Path, files: list[Path]) -> str:
    result = hashlib.sha256()
    for path in files:
        require(path.is_file() and not path.is_symlink(), f"Not a regular file: {path}")
        name = path.relative_to(workspace).as_posix().encode("utf-8")
        data = path.read_bytes()
        result.update(len(name).to_bytes(8, "big"))
        result.update(name)
        result.update(len(data).to_bytes(8, "big"))
        result.update(data)
    return result.hexdigest()


def verify(root: Path) -> None:
    manifest = json.loads((root / "verification.json").read_text())
    require(manifest["schema_version"] == 1, "Unsupported manifest version")
    require(manifest["declared_model"] == "Forall (Astrio)", "Wrong credit label")
    require(set(manifest["problems"]) == EXPECTED_PROBLEMS, "Wrong problem set")
    receipts = json.loads((root / "accepted-results.json").read_text())
    require(receipts["schema_version"] == 2, "Unsupported official result schema")
    require(receipts["user"] == manifest["submitter"], "Submitter mismatch")
    require(len(receipts["results"]) == len(EXPECTED_PROBLEMS), "Wrong result count")
    official = {record["problem_id"]: record for record in receipts["results"]}
    require(set(official) == EXPECTED_PROBLEMS, "Wrong official problem set")
    expected = set(ROOT_FILES)
    for problem, record in manifest["problems"].items():
        receipt = official[problem]
        require(receipt["declared_model"] == manifest["declared_model"], "Model mismatch")
        require(receipt["statement_revision"] == record["statement_revision"],
                "Statement revision mismatch")
        require(receipt["submission"]["ref"] == manifest["accepted_source_commit"],
                "Accepted source commit mismatch")
        require(receipt["submission"]["repo"] == manifest["source_repository"],
                "Original source repository mismatch")
        require(receipt["benchmark_commit"] == manifest["official_benchmark_commit"],
                "Official benchmark commit mismatch")
        require(receipt["intake"]["kind"] == "server", "Unexpected intake kind")
        require(receipt["intake"]["submission_id"] == record["submission_id"],
                "Submission ID mismatch")
        require(receipt["result_id"] == record["result_id"], "Result ID mismatch")
        require(receipt["accepted_at"] == record["accepted_at"], "Acceptance time mismatch")
        workspace = root / "proofs" / problem
        config = tomllib.loads((workspace / "lakefile.toml").read_text())
        require(config["name"] == problem, f"Wrong Lake name: {problem}")
        require(record["problem_group"] == "software-verification", "Wrong group")
        require(record["statement_revision"] == 1, "Wrong statement revision")
        solver = [workspace / "Submission.lean"] + sorted(
            (workspace / "Submission").rglob("*.lean")
        )
        require(len(solver) == record["solver_file_count"], f"File-count mismatch: {problem}")
        actual = digest(workspace, solver)
        require(actual == record["candidate_sha256"], f"Solver digest mismatch: {problem}")
        support = [workspace / name for name in sorted(SUPPORT_FILES)]
        require(digest(workspace, support) == record["support_sha256"],
                f"Trusted support-file digest mismatch: {problem}")
        for path in solver:
            # Heuristic only; recorded kernel checks establish axiom validity.
            # Historical audit comments mention sorryAx without invoking it.
            require(not re.search(r"\b(?:sorry|admit)\b", path.read_text()),
                    f"Admission marker requires inspection: {path.relative_to(root)}")
        expected.update(path.relative_to(root).as_posix() for path in solver + support)
        print(f"PASS {problem}: {len(solver)} solver files, accepted SHA256 {actual}")

    actual_files = set()
    for directory, dirs, files in os.walk(root, followlinks=False):
        base = Path(directory)
        if base == root and ".git" in dirs:
            dirs.remove(".git")
        if base in (root / "proofs" / problem for problem in EXPECTED_PROBLEMS):
            if ".lake" in dirs:
                dirs.remove(".lake")
        if "__pycache__" in dirs:
            dirs.remove("__pycache__")
        for name in dirs + files:
            require(not (base / name).is_symlink(), f"Symlink not allowed: {base / name}")
        for name in files:
            path = base / name
            if base == root and name == ".git":
                continue
            relative = path.relative_to(root).as_posix()
            actual_files.add(relative)
            text = path.read_text(encoding="utf-8")
            require(not re.search(
                r"/(?:Users|var/folders)/|-----BEGIN (?:RSA |EC |OPENSSH )?PRIVATE KEY-----"
                r"|github_pat_[A-Za-z0-9_]{20,}|gh[pousr]_[A-Za-z0-9]{20,}", text
            ), f"Possible private path or credential: {relative}")
    require(actual_files == expected,
            f"Unexpected/missing files: extra={sorted(actual_files - expected)}, "
            f"missing={sorted(expected - actual_files)}")
    print(f"PASS source-only layout: {len(actual_files)} files; no unexpected files or symlinks")
    print("PASS accepted-result metadata matches the saved official records")
    print("This checks packaging integrity, not a new Lean build or a live leaderboard query.")


if __name__ == "__main__":
    try:
        verify(Path(__file__).resolve().parent.parent)
    except (ValueError, KeyError, OSError) as error:
        print(f"FAIL: {error}", file=sys.stderr)
        raise SystemExit(1)
