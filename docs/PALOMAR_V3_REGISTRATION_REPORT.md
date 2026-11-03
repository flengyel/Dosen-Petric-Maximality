# Palomar version 3 registered — 3 November 2026

Registered:
[PALOMAR-2026-10-30-000014, version 3](https://palomar-registry.org/entry?id=PALOMAR-2026-10-30-000014&version=3).
Submission: `j92h1fl2enqs`. Exact source:
**`76a4ea71f257746bb6ea2cb2e686e85914c7347c`**, repository
`flengyel/Dosen-Petric-Maximality`, repository-root `comparator.json` and
`formalization.yaml`, Lean **4.35.0**. The durable release tag
**`dosen-petric-v25-palomar-v3`** resolves to that source locally and remotely.
No version or commit mismatch was found.

## Review acceptance and registration

The exact author-facing review and its service digest were retrieved at
15:00:52 UTC. The author had the existing private submission page open and
accepted the review there. Palomar records the registration request at
15:00:59 UTC. The exact response, service digest and complete candidate public
metadata were also delivered privately to Downloads and byte-verified at
15:02:00 UTC. The author then reported, “I have accepted.”

Authenticated readback at 15:07:04 UTC confirmed `registration_consent: true`.
The status API did not echo the consent digest; this report does not claim
otherwise. The separately retrieved review digest remained the same as the
originally delivered digest. The agent did not POST another registration
request or treat the earlier intake approval as consent to this review.

The public record gives `registered_at: 2026-11-03T15:09:39Z`. Palomar recorded
finalization at 15:12:11 UTC. Authenticated readback at 15:19:09 UTC confirmed
`status: registered`, consent and the exact version-specific public URL.

The original review, its consent digest and bearer credential remain in ignored
private staging. The private Downloads files are in
`/mnt/c/Users/fleng/Downloads/Dosen-Petric-Palomar-v3-Private-20261103/`:
`Palomar-v3-exact-review.json`, `Palomar-v3-review-and-registration.md` and
`Palomar-v3-public-metadata.yaml`. The JSON is the exact returned API response;
the Markdown includes that full response, its service digest, the complete
public metadata and the publication explanation. None of those private review
or consent files was added to public Git.

## Verification and published review

The exact-candidate official full preflight
[41580971518](https://github.com/flengyel/Dosen-Petric-Maximality/actions/runs/41580971518)
passed in full mode under `palomar-standard-v1`. Its mechanical-report hash is
`61c666fbe96eea6346716ab7ceafa7a3ffa4e13e9ea1633e65fb5aefe5a8706b`.
The distinct service verification
[41587644731](https://github.com/PalomarRegistry/PalomarSubmission/actions/runs/41587644731)
passed under `palomar-namespace-16x32-v1`, with report hash
`a99c3d7e48ac5383e9c3f6bad564284f836eeab879e1fe2c4d1f5f8d0a0066b8`.
Both reports have `status: pass` and `errors: []`. Lean, NanoDa and protected
con-ron accepted; con-ron checked 9,639 declarations. The successful checks
were reused. Ordinary Lean CI or a prior-version check was not substituted
for full preflight at the exact candidate.

The selected declarations, modules, shared-definition list, permitted axioms
and source/configuration hashes were checked against the frozen source.
Proof and verifier inputs are unchanged from registered version 2. The
mechanical audit-surface warning remains: the Challenge has 572 lines, above
the preferred 300-line surface and within the hard cap. This is distinct from
an editorial warning.

The publicly archived review records outcome `neutral`, no material findings,
no requested changes and no editorial warnings. Its reviewer is
`codex:gpt-6-sol`, reviewed at 07:19:09 UTC under policy
`28bd48b9b71bbb2a82c718ce761d5a4220ef8e60`. Its exact summary is:

> Mechanical verification passed, and the completed editorial checks identified no blocking problem with the selected statements, their presentation, or their research interest. This review does not constitute registration or endorsement.

The archived-review hash is
`bdd0ff7cd9e32608dd825b43f863997452c764dc89679c9cd21ca14c177a591a`.
This is the public archived-review hash, distinct from the privately retained
service consent digest. The complete published review is retained in
`provenance/palomar-v3-registration-20261103/evidence/review.json`.

## Public wording and publication effect

The title and abstract match the exact candidate metadata:

**Maximality of the Došen–Petrić Boolean Category**

> Let P be a nonempty set of propositional variables. The freely generated zero-identity Boolean category B(P) of Došen and Petrić is maximal: every congruence on its morphisms preserved by the operations on morphisms and uniform formula substitution is either equality or identifies every pair of parallel morphisms. The formalization gives two proofs of maximality and proves the congruence dichotomy. It also proves that the identity and zero endomorphism of each variable are distinct, and that there is no morphism from the terminal object to the initial object.

The registered metadata cites manuscript version 25 through the durable release
tag, with Sections 2–6 and Appendices A–E. The complete public record is
retained byte for byte as `provenance/palomar-v3-registration-20261103/entry.json`.
The v3 citation in `manuscript/palomar_v25.bib` now names a confirmed record at
the intended source. No floating latest-version URL was substituted.

Registration permanently publishes the versioned registry record and submitted
public metadata, exact source, declared maintainer relationship, redacted
archived review with its outcome and material findings, reviewer model
identifiers, mechanical workflow and policy revision, rendered Challenge
material and source-preservation evidence. It creates an immutable
record-specific native archive tag. Scores, per-finding severities and internal
audit notes are excluded from the public archived review. The authenticating
GitHub account is not added as a submitter field. Earlier registered versions
remain part of the publication history.

## Public readback and source preservation

The public entry, versions index and exact registration-identity index agree
on version 3 at the intended commit. Versions 1 and 2 remain registered and
their entry files retain their original commits,
`2e771844077fd8cebfbe365230f13d4dd13a75b1` and
`5dbee39bea09539bd130f729e82636419f71f920`.

All **four** evidence-manifest files match their recorded byte counts and
SHA-256 values. The archived mechanical report is byte-identical to the service
artifact. The evidence-tree hash is
`db3958ea3264452f73b9a569411387332d08ba3e572b0b9c087fbbac71a38249`.
All **13/13** served render files match their manifest bytes. The render-tree
hash is `3837ef5166cef1fdb7ec321886f59100eecf745017c5106a0fd70945df09fda3`.
The rendered opening matches the submitted Challenge; the five rendered
statement types agree with version 2. No served-render mismatch was found.

The native archive is
`PalomarArchive/flengyel--Dosen-Petric-Maximality--63db84754d7f`. Its immutable
preservation ref is
`refs/tags/palomar/PALOMAR-2026-10-30-000014-v3/76a4ea71f257746bb6ea2cb2e686e85914c7347c`.
Git readback resolves it to the submitted commit. The preservation-receipt
hash is `fd2fad3296000fe04a8fedbf3b36187aa3fa3c23cb4e8c4b64a744838f951704`.
The durable author release tag was separately checked locally and remotely at
the same commit and was not altered.

## Interruption, preservation and delivery

Earlier intake requests received temporary HTTP 503 errors. The later
authenticated transaction succeeded and its temporary tag and fresh secret
gist were deleted immediately, with HTTP 404 readbacks. Subsequent status and
review retrieval encountered HTTP 500 errors. Automatic polling was paused
to reduce requests during the interruption. A later manual check recovered
the completed review. The errors did not require a new submission, repeated
successful checks or a changed candidate. Their server-side cause was not
established. The preceding report is preserved byte for byte at
`docs/history/PALOMAR_V3_UPDATE_STATUS_BEFORE_REGISTRATION_20261103.md`.

The frozen manuscript, PDF, source package, metadata, release links, proofs,
earlier releases and stash remain unchanged. The candidate's preparation-time
statements about pending registration remain in its immutable snapshot; this
separate report records the later completed publication. No arXiv upload or
new mathematical development occurred.

Public evidence and validation are retained under
`provenance/palomar-v3-registration-20261103/`. Only the publicly registered
archived review is included there. Reports and selected evidence are copied
from committed bytes to
`/mnt/c/Users/fleng/Downloads/Dosen-Petric-Palomar-v3-20261103/`, with differing
existing copies preserved. The delivery receipt records exact filenames,
SHA-256 values and byte verification. No further consent, registration request
or service polling is required for this update.
