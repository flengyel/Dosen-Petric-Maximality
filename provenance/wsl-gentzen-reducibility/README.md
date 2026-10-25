# Evidence use

The checked source inventory and command JSON files identify the exact proof
candidate. RAW_LOGS.tar.gz preserves every raw log byte, including failed
elaborations and the first staged whitespace rejection. Extract this archive
in this directory before checking individual log hashes from the command JSON.
Raw .log files remain available locally but are ignored by Git; the archive
is the committed representation. EVIDENCE_SHA256SUMS inventories the committed
metadata, controls and archives, excluding its own bytes and the raw logs.

PRESERVED_RECONCILIATION.tar.gz preserves original competing drafts, status,
diffs and untracked input files. FORMAT_ONLY_IMPORTS.json records the sole
format change made to the imported instruction and supplied review: removing
redundant blank lines at EOF. Their exact original bytes remain archived.
No production Lean source changed after the passing final build.
