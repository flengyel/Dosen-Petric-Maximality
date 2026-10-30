# Official-preflight metadata correction

A final evidence audit found a nonempty `temp_clone_token` field in one retained
GitHub repository-metadata command log. That response was mistakenly included
with public provenance. The field is now redacted in the current repository and
local staging copies, and the capture helper now redacts credential fields in
JSON before writing command logs.

GitHub's [Get a repository documentation](https://docs.github.com/en/rest/repos/repos#get-a-repository)
states that this credential grants read-only Git access to that repository,
expires five minutes after generation, and cannot push changes. The response
was logged at `2026-10-30T21:12:24.241655+00:00`. Its first public commit was
`3b94aac1a7066f1ec21aabd676d6ac8012694d5d` at `2026-10-30T17:30:43-04:00`, more than eighteen minutes later.
Under that documented lifetime it had already expired before the commit that
published the log. No claim of independent token revocation or testing is made;
the value was neither printed nor used during this audit.

The audit searched every tracked current file for the discovered value and
found it only in that metadata log. After redaction it appears in no tracked
current file. The expired value remains in historical commit `3b94aac1a7066f1ec21aabd676d6ac8012694d5d`;
history was preserved without a reset or force-push. The Windows GitHub CLI
account credential was not included in the metadata field or extracted by this
process. This correction does not change the proof source, any Comparator
input, the official report, or the downloaded official ZIP.

Immutable submission: `2e771844077fd8cebfbe365230f13d4dd13a75b1`.
Official mechanical JSON SHA-256:
`b21cdb78ae39b47b11e96be06a388787cd8d6d8ace045e4d403fb50cd14db8c9`.
Official artifact ZIP SHA-256:
`d6b0921b4b8d6b237a39c8d47e760fbb3a47b435877ff59dcd6d06a3957e36ff`.

No Palomar service token, intake, private review or registration was involved.
Publication order remains Palomar registration first, then arXiv.
