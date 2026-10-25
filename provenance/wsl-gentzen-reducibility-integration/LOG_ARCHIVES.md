# Verification diagnostics

The repository ignores raw *.log files. Every complete raw diagnostic log is
therefore committed here as verification/<raw-name>.gz, without changing its
bytes. LOG_ARCHIVES.json records both compressed and decompressed hashes.
Raw copies remain locally in .codex-work/ and this provenance directory.
Decompress an archive to inspect the exact diagnostics referenced by a receipt.
SHA256SUMS lists committed archives rather than absent ignored raw copies.
