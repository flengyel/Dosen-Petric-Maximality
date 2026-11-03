# Palomar v3 update: preflight passed; intake unavailable

3 November 2026. The requested update is **not registered**. The remaining
work is blocked at Palomar's intake service, before authentication or service
verification. No review has been received and no registration decision has
been requested from the author.

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

No request returned a pending secret, challenge, submission ID or bearer
credential. No temporary authentication tag or secret gist was created.
There is therefore no authenticated v3 status/approval URL, no service
verification result, and no review to approve. No registration request was
made. The author has not approved unseen review material.

The versions, repository and exact registration-identity indexes were read
before intake and rechecked before the attempts. They identify the existing
result, registered versions 1 and 2, and the original registered commits.
The candidate is not in the registered-commit list. Version 3 remains
unconfirmed, as does the prepared citation's publication condition.

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

When intake is restored, recheck the registration identity and expected
successor, then resume the ordinary update using this exact candidate and
the passed full preflight. Complete the temporary-tag/fresh-secret-gist proof
in one sitting and delete its artifacts after successful verification.
Deliver the exact returned review and its service digest privately, explain
permanent publication of the record, source-preservation evidence and
redacted archived review, and obtain the author's decision on those bytes.
Only then send the digest-bound registration request. Verify public version
3 at the exact candidate before describing the prepared citation as confirmed.
Any different version or commit stops final publication; the tag must remain.

Both reports and the selected public evidence are delivered from committed
bytes to `/mnt/c/Users/fleng/Downloads/Dosen-Petric-Palomar-v3-20261103/`, with
conflict preservation and a verified delivery receipt. This status does not
claim completion of the requested registration.
