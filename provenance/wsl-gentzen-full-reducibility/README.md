# Full Reducibility verification evidence

All paths in LOG_ARCHIVES.json refer to retained gzip archives. Each decompresses
to the recorded raw-log hash and was compared with its original raw log.
COMMANDS.json retains successes and 84 nonzero receipt rows; failed
elaborations are not counted as completed theorems. Final commands and exact
source inventory are separate from the historical baseline and later record-only
checks. The source/PDF cache hashes are in the report. Final Git and Downloads
receipts are written after committing and compare against Git blobs, avoiding
a self-referential commit hash in the report. Both full producers are complete;
containing transport and the full-paper endpoint are not.
