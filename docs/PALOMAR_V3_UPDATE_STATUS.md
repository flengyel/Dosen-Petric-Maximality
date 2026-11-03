# Palomar v3 update: verification passed; status and review APIs unavailable

3 November 2026. The ordinary update was authenticated as submission
**`j92h1fl2enqs`** at 06:04:55 UTC, after the earlier temporary intake failures.
Palomar has completed mechanical verification of the exact candidate with
`status: pass` and no errors. The requested update is **not registered**. The
last confirmed service state was `awaiting-review`. The status and review APIs
now return HTTP 500, so current review progress cannot be confirmed. No
registration request has been made.

## Fixed release and completed preflight

- Repository: `flengyel/Dosen-Petric-Maximality`.
- Exact candidate: `76a4ea71f257746bb6ea2cb2e686e85914c7347c`.
- Durable tag: `dosen-petric-v25-palomar-v3`, verified at that candidate.
- Existing registry ID: `PALOMAR-2026-10-30-000014`.
- Intended version: 3; latest confirmed registered version: 2.
- Project root; `comparator.json`; `formalization.yaml`.
- [Passing official full preflight, run 41580971518](https://github.com/flengyel/Dosen-Petric-Maximality/actions/runs/41580971518).

The [separate preflight report](PALOMAR_V3_PREFLIGHT_REPORT.md) records the
complete report, exact input/hash checks and successful Lean, NanoDa and
con-ron verification. The report has `status: pass` and `errors: []`; con-ron
accepted 9,639 declarations. This exact-candidate preflight must be reused
when continuing, unless a relevant input or protocol requirement changes.

## Intake outcome

The existing authenticated Windows GitHub CLI account has repository
push/maintain access and repo, workflow and gist scopes. No repository tag
ruleset was reported. The ordinary existing-ID update request was prepared
for the exact candidate with authorization relationship `maintainer`.

Four spaced requests to `POST https://submit.palomar-registry.org/api/submit`
received HTTP **503**, each with exactly this response:

```json
{"error":"submission intake is temporarily unavailable"}
```

The response times were 05:30:56, 05:34:12, 05:37:39 and 05:50:45 UTC on
3 November 2026. The fourth attempt followed the pause spent delivering the
reports and returned the same refusal. No Retry-After value was available in the retained retry response
headers; the retries were separated by more than three minutes. A separate
`GET /healthz` returned HTTP 200 with `{"ok":true}`. That endpoint confirms
the Worker responds; it does not establish that intake is available.

The live server's [public source](https://github.com/PalomarRegistry/PalomarServer/blob/main/src/index.js)
identifies this as a service-side refusal.
Its generic health response does not diagnose the underlying operational
cause. No candidate error or required source correction was returned.

There is no two-version limit in the ordinary-update policy: later updates
receive the next integer version. The limit of two applies to simultaneous
verifications for one repository owner, with a separate limit of one for a
submitter. The observed response is the generic temporary-intake 503, not
an admission-limit 429. It does not establish an account suspension. The
public code can issue this generic refusal when its intake limiter is missing
or pending-state listing fails; only server-side diagnostics distinguish them.

The retry at approximately 06:04 UTC succeeded. The registration identity
and version index were checked immediately before intake: the existing record
still had versions 1 and 2 and did not include the candidate. The ordinary
request named the existing registry ID and exact candidate.

The documented temporary tag and fresh secret gist established the saved
account's access. Authentication returned submission `j92h1fl2enqs` at
06:04:55 UTC. Both temporary artifacts were deleted immediately; readback
confirmed HTTP 404 for each at 06:05:00 UTC. The durable release tag was not
used as an authentication tag and was not changed.

The [service verification workflow, run 41587644731](https://github.com/PalomarRegistry/PalomarSubmission/actions/runs/41587644731)
completed successfully. Its complete mechanical report has `status: pass`,
`phase: verification`, `stage: complete` and `errors: []`. The exact source,
root configuration, five selected declarations and input hashes were checked
against the fixed candidate. Lean, NanoDa and con-ron passed. The separate
[service verification report](PALOMAR_V3_SERVICE_VERIFICATION_REPORT.md)
records the evidence. The last successful authenticated check, at 06:26:12 UTC,
reported `awaiting-review`; no review has been retrieved. The private status-page shortcut was
delivered under `Downloads/Dosen-Petric-Palomar-v3-Private-20261103/`; it
contains a bearer credential and is excluded from Git.

Version 3 remains unconfirmed, as does the prepared citation's publication
condition. The author has not approved unseen review material. Opening the
submission page does not constitute a registration instruction.

## Refresh failure after successful verification

The author's submission page reported “Could not refresh this submission.
Retrying.” The saved authenticated status request returned HTTP **500** at
06:31:13 UTC and again at 06:44:37 UTC. A separate request to the review
endpoint returned HTTP **500** at 06:45:11 UTC. Both endpoints served the
generic HTML error page titled “Palomar could not complete that just now —
Palomar”, rather than their normal JSON response.

A contemporaneous health request returned HTTP 200 with `{"ok":true}`; that
generic endpoint does not establish that submission status or review retrieval
works. The independent public version index remained available at 06:45:53
UTC and listed registered versions 1 and 2 only. It did not list version 3.

This is a server-side refresh/retrieval failure. No failed proof check or
requested candidate correction was returned. The retained full preflight and
service mechanical verification remain passing results; current review
progress is unknown while these endpoints fail. No review, service consent
digest or registration confirmation has been received.

The background monitor stopped at the first HTML error because its code tried
to parse that response as successful status JSON. This local error handling
has been corrected: non-200 responses leave the last confirmed state intact,
are retained privately, and are followed by the required wait before another
check. Monitoring continues against the same submission. No new intake or
verification has been started.

## Preserved state and continuation

The release tag was never moved, deleted or recreated. The manuscript, PDF,
source package, metadata, release links, proofs and verifier inputs remain
unchanged. All earlier versions and the existing stash remain. No arXiv upload
or new mathematical development was performed.

The complete passing preflight and its validation are retained in
`provenance/palomar-v3-preflight-20261103/`; the sanitized service summary is
`provenance/palomar-v3-update-20261103/service-stage-summary.json`.
Exact private requests/responses and the guarded continuation helpers remain
under `.codex-work/palomar-v3-update-20261103/`, outside public Git.

Continue the existing authenticated submission, using the saved private
state. Do not create another submission or repeat the passed exact-candidate
full preflight. Respect the service's status/review polling limits. The passed service
mechanical report and its validation are retained in
`provenance/palomar-v3-service-20261103/`.

Deliver the exact returned review and its service digest privately, explain
permanent publication of the record, source-preservation evidence and
redacted archived review, and obtain the author's decision on those bytes.
Only then send the digest-bound registration request. Verify public version
3 at the exact candidate before describing the prepared citation as confirmed.
Any different version or commit stops final publication; the tag must remain.

The reports and selected public evidence are delivered from committed
bytes to `/mnt/c/Users/fleng/Downloads/Dosen-Petric-Palomar-v3-20261103/`, with
conflict preservation and a verified delivery receipt. This status does not
claim completion of the requested registration.
