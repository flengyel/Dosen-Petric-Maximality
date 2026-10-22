#!/usr/bin/env bash
set -euo pipefail
root=$(CDPATH= cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
dest="$root/.codex-work/upstream/PalomarSubmission"
pin=5cfaefe2f4c18f237c63d9635f9f54ab68785d89
if [[ -e $dest ]]; then
  [[ -d $dest/.git ]] || { echo 'Upstream destination is not a Git checkout.' >&2; exit 1; }
  [[ $(git -C "$dest" rev-parse HEAD) == "$pin" ]] || {
    echo 'Existing upstream checkout has a different revision; preserve and inspect it.' >&2; exit 1;
  }
  [[ -z $(git -C "$dest" status --porcelain) ]] || {
    echo 'Existing upstream checkout has changes; preserve and inspect it.' >&2; exit 1;
  }
else
  mkdir -p "$(dirname -- "$dest")"
  git init "$dest"
  git -C "$dest" remote add origin https://github.com/PalomarRegistry/PalomarSubmission.git
  git -C "$dest" fetch --depth=1 origin "$pin"
  git -C "$dest" checkout --detach FETCH_HEAD
fi
[[ $(git -C "$dest" rev-parse HEAD) == "$pin" ]]
printf 'Pinned verifier source: %s\n' "$dest"
echo 'No verifier or submission service has been invoked.'
