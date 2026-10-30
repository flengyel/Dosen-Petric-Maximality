# Palomar source-layout record

The registration candidate retains all historical evidence. Four historical
PublicTypes fixtures did not begin with `module`; they are retained as `.lean.txt`
with exactly their original bytes. No production source or failed production
proof was reclassified. The immutable old reports and checksum manifests keep
the paths and claims of their original commits. The mapping below resolves those
historical references in this candidate; `scripts/resolve-historical-evidence.py`
checks the retained bytes before returning their current path.

| Original historical path | Current retained path | SHA-256 |
| --- | --- | --- |
| `provenance/wsl-gentzen-blocked-classification/PublicTypes.lean` | `provenance/wsl-gentzen-blocked-classification/PublicTypes.lean.txt` | `b7171dd4233d46239b33e7c8553b1dfef0cb0de01cccc423fe8f6dae24c5810c` |
| `provenance/wsl-gentzen-proof-replacement/PublicTypes.lean` | `provenance/wsl-gentzen-proof-replacement/PublicTypes.lean.txt` | `461b6081a05f90dc874f3741fd108529ae54c7fa62eba5f090bdd4f02709d2ab` |
| `provenance/wsl-gentzen-reducibility-integration/verification/PublicTypes.lean` | `provenance/wsl-gentzen-reducibility-integration/verification/PublicTypes.lean.txt` | `46aac9dcab0d564a653071ce03df647ac8faa610408fffedd77057e9b65f06e7` |
| `provenance/wsl-gentzen-w5-other-premise-mix/PublicTypes.lean` | `provenance/wsl-gentzen-w5-other-premise-mix/PublicTypes.lean.txt` | `62fe2eae3738146b4e9b2803ac7daf52b53f089768ae5c1f79cb93dd7b6b3410` |

The machine-readable mapping includes every located explicit path reference.
All other historical source/evidence bytes are preserved. The final whole-tree
scan covers every committed Lean file, beyond the production checker, and also
checks line limits, symlinks, binary artifacts, LFS pointers and submodules.
Exact final counts and source-closure status are recorded in the current
registration verification report. This layout repair does not change a theorem,
generator, equation, side condition or manuscript claim.
