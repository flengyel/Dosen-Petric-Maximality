# Palomar update preparation for manuscript v24

3 November 2026. Existing identifier: `PALOMAR-2026-10-30-000014`.
Registered version 2 remains the citation in the paper. No new registry version
has been submitted or registered from this environment.

The v24 paper and descriptive metadata are prepared for the author's requested
ordinary update. Root `formalization.yaml` is updated from its v13 manuscript
description to v24. Historical reviews and registered source commits remain.
The five Comparator selections, permitted axioms, classifications, namespace,
source modules and proof statuses are unchanged. The metadata pins the v24
paper commit; it does not claim a new proof build or registration.

The publication uses two commits. The first contains the corrected paper,
package, reviews and build evidence. The second pins that immutable first
commit in `formalization.yaml` and includes the Codex service handoff. Submit
the full 40-character second commit as the new candidate, after the required
full preflight at exactly that commit. This avoids a self-referential source
URL in the metadata.

[Codex continuation instructions](PALOMAR_V24_CODEX_HANDOFF.md) give the exact
repository, paths, existing identifier, candidate-resolution commands and
authentication sequence. The candidate commit message is
`Synchronize v24 Palomar metadata and Codex handoff`.

## Tag distinction and service requirements

The documented authentication tag has the form
`refs/tags/palomar-verify-CHALLENGE`. It is a temporary challenge proof used
together with a newly created secret gist, and is deleted after verification.
Pushing that tag does not itself update the registry. A durable release tag
may identify a snapshot, but its exact previously discussed name was not recovered.
Do not invent it or move the registry's immutable preservation tags.

The source repository has no tag-driven Palomar registration workflow. Its
`palomar-preflight.yml` is manually dispatched. An ordinary update takes the
exact candidate commit and the existing registry identifier. It requires
the full candidate preflight, intake authentication, service verification and
review, then the author's approval of the exact returned review before the
digest-bound registration request. The earlier v2 approval applies to v2.

The present environment can publish repository commits but has no authenticated
`gh` and exposes no connector operation to create the required tag and gist.
No partial, expiring intake was started. Codex in the author's authenticated
environment can complete those steps from the committed handoff.

Protocol source: [Palomar agent instructions](https://submit.palomar-registry.org/llms.txt).
Existing evidence: [v2 registration report](PALOMAR_V2_REGISTRATION_REPORT.md).
Preserve all v1/v2 snapshots and citations until a successor has been registered
and publicly verified. Do not automate the Palomar browser login or publish
private challenge material, credentials or an unregistered private review.
