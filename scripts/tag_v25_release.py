"""Create the fixed v25 source tag after validating the release manifest."""

from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import subprocess
import sys

REPOSITORY = "flengyel/Dosen-Petric-Maximality"
TAG = "dosen-petric-v25-palomar-v3"
TAG_REF = f"refs/tags/{TAG}"
MANIFEST = "provenance/palomar-v3-candidate/release-v25.json"
REQUIRED_ARTIFACTS = {
    "manuscript/Maximality_of_the_Dosen_Petric_Boolean_Category_v25.tex",
    "manuscript/Maximality_of_the_Dosen_Petric_Boolean_Category_v25.pdf",
    "formalization.yaml",
}


def git(*args: str) -> str:
    return subprocess.check_output(["git", *args], text=True).strip()


def object_bytes(commit: str, path: str) -> bytes:
    return subprocess.check_output(["git", "show", f"{commit}:{path}"])


def remote_target() -> str | None:
    lines = git("ls-remote", "origin", TAG_REF, TAG_REF + "^{}").splitlines()
    refs = dict(reversed(line.split("\t", 1)) for line in lines if line)
    return refs.get(TAG_REF + "^{}", refs.get(TAG_REF))


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def validate_candidate() -> tuple[str, str]:
    require(os.environ.get("GITHUB_REPOSITORY") == REPOSITORY, "Unexpected repository")
    require(os.environ.get("GITHUB_REF") == "refs/heads/main", "Expected a main-branch push")
    commit = os.environ.get("GITHUB_SHA", "")
    require(bool(re.fullmatch(r"[0-9a-f]{40}", commit)), "Invalid candidate SHA")
    require(git("rev-parse", "HEAD") == commit, "Checkout differs from GITHUB_SHA")
    require(git("cat-file", "-t", commit) == "commit", "Candidate is not a commit")

    changed = git("diff-tree", "--root", "--no-commit-id", "--name-only", "-r", commit)
    require(MANIFEST in changed.splitlines(), "The candidate must add or change the release manifest")

    manifest_bytes = object_bytes(commit, MANIFEST)
    manifest = json.loads(manifest_bytes)
    require(isinstance(manifest, dict), "The release manifest must be a JSON object")
    expected = {
        "tag": TAG,
        "manuscript_version": 25,
        "registry_id": "PALOMAR-2026-10-30-000014",
        "anticipated_registry_version": 3,
        "registry_status": "pending",
    }
    for key, value in expected.items():
        require(manifest.get(key) == value, f"Unexpected manifest field: {key}")

    artifacts = manifest.get("artifacts")
    require(isinstance(artifacts, dict), "artifacts must map paths to SHA-256 digests")
    require(REQUIRED_ARTIFACTS <= artifacts.keys(), "Required release artifacts are missing")
    for path, expected_digest in artifacts.items():
        require(isinstance(path, str), "Artifact paths must be strings")
        parsed = PurePosixPath(path)
        require(
            not parsed.is_absolute() and ".." not in parsed.parts and str(parsed) == path,
            "Artifact paths must be normalized repository-relative paths",
        )
        require(
            isinstance(expected_digest, str)
            and bool(re.fullmatch(r"[0-9a-f]{64}", expected_digest)),
            f"Invalid SHA-256 for {path}",
        )
        entry = git("ls-tree", commit, "--", path)
        require(bool(entry), f"Artifact is not tracked: {path}")
        header, tracked_path = entry.split("\t", 1)
        mode, kind, _ = header.split()
        require(
            tracked_path == path and mode in {"100644", "100755"} and kind == "blob",
            f"Artifact is not a regular tracked file: {path}",
        )
        digest = hashlib.sha256(object_bytes(commit, path)).hexdigest()
        require(digest == expected_digest, f"Artifact hash mismatch: {path}")
    return commit, hashlib.sha256(manifest_bytes).hexdigest()


def main() -> None:
    commit, manifest_digest = validate_candidate()
    existing = remote_target()
    require(existing in {None, commit}, f"Refusing to replace existing tag {TAG}: {existing}")
    if existing is None:
        pushed = subprocess.run(["git", "push", "origin", f"{commit}:{TAG_REF}"], check=False)
        # A concurrent identical creation is harmless; every other failed push is fatal.
        if pushed.returncode:
            require(remote_target() == commit, "Tag push failed; no replacement was attempted")
    require(remote_target() == commit, "Remote tag readback differs from the candidate")

    summary = (
        f"Release tag: {TAG}\n\n"
        f"Candidate commit: {commit}\n\n"
        f"Manifest SHA-256: {manifest_digest}\n\n"
        "The tag was verified remotely. Palomar registration remains pending.\n"
    )
    print(summary)
    if os.environ.get("GITHUB_STEP_SUMMARY"):
        with Path(os.environ["GITHUB_STEP_SUMMARY"]).open("a") as stream:
            stream.write(summary)


if __name__ == "__main__":
    try:
        main()
    except (RuntimeError, ValueError, TypeError, subprocess.CalledProcessError) as exc:
        print(f"Release tag failed: {exc}", file=sys.stderr)
        sys.exit(1)

