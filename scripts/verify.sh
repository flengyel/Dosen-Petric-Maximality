#!/usr/bin/env bash
set -euo pipefail
root=$(CDPATH= cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
cd "$root"
export LEAN_NUM_THREADS=1
out="$root/.codex-work/verification"
mkdir -p "$out"
exec 9>"$root/.codex-work/build.lock"
flock -n 9 || { echo 'Another project verification is running.' >&2; exit 1; }
exec > >(tee "$out/verify.log") 2>&1
date -u '+%Y-%m-%dT%H:%M:%SZ'
git rev-parse HEAD
git status --short
python3 scripts/check-source.py
lean --version
lake --version
expected=$(cat lean-toolchain)
[[ $expected == leanprover/lean4:v4.35.0 ]] || { echo 'Unexpected toolchain pin.'; exit 1; }
lean --version | grep -Eq 'version 4\.35\.0[, )]' || { echo 'Wrong active Lean version.'; exit 1; }
lake build
cp lake-manifest.json "$out/lake-manifest.json"
cat lake-manifest.json
lake env lean -DwarningAsError=true Checks/Axioms.lean
echo 'PASS: build and transitive axiom audit. See the registration report for separate Comparator/kernel and official preflight statuses.'
