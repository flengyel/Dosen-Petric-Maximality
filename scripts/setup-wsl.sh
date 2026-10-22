#!/usr/bin/env bash
set -euo pipefail
root=$(CDPATH= cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
expected=/home/flengyel/src/Dosen-Petric-Maximality
[[ $root == "$expected" ]] || {
  printf 'Expected checkout at %s; found %s. No installation performed.\n' "$expected" "$root" >&2
  exit 1
}
[[ $(id -u) != 0 ]] || { echo 'Run as flengyel, not root.' >&2; exit 1; }
cd "$root"
export PATH="$HOME/.elan/bin:$PATH"
for command_name in git python3 elan flock; do
  command -v "$command_name" >/dev/null || {
    printf 'Missing required command: %s\n' "$command_name" >&2
    exit 1
  }
done
git status --short --branch
[[ $(cat lean-toolchain) == leanprover/lean4:v4.35.0 ]] || {
  echo 'Unexpected toolchain pin. Review before installing.' >&2; exit 1;
}
elan toolchain install leanprover/lean4:v4.35.0
bash scripts/verify.sh
