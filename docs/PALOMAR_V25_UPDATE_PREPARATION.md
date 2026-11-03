# Fixed release for the Palomar v3 update

Release name: `dosen-petric-v25-palomar-v3`. Existing identifier: `PALOMAR-2026-10-30-000014`.
Anticipated new registry version: 3. Registry status: pending.

The paper's source hyperlinks and metadata's paper/claim-map references use
the fixed release name. The final candidate is the commit named by that tag.
The prepared version-3 citation is conditional on the service issuing that
record at the exact candidate. No registry version has been registered here.

The one-shot release workflow reads
`provenance/palomar-v3-candidate/release-v25.json`, verifies artifact hashes,
creates the tag only if absent and verifies its remote target. A pre-existing
different target fails; it is never overwritten. This workflow creates the
source tag only. It does not submit or register with Palomar.

The [Codex handoff](PALOMAR_V25_CODEX_HANDOFF.md) resolves the full commit,
verifies it against the tag, runs the official full preflight for that candidate,
and gives the ordinary-update procedure. The temporary authentication tag and
secret gist are separate from the fixed source-release tag.

The v24 candidate `c23fc48a109a08e74dae6ade9dcc9ee665b6f224` is superseded.
Do not submit it. Preserve its files and the registered v1/v2 evidence.
After successful v3 registration and exact readback, this prepared paper needs
no later citation edit. Any other version outcome must be resolved before
final publication, without moving the tag.
