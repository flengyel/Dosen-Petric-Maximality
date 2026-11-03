# Codex continuation: v25 fixed release and Palomar v3 candidate

Prepared 2 November 2026 in the author's local date. Complete the authorized ordinary update for **flengyel/Dosen-Petric-Maximality**, using one source commit for the manuscript, PDF, Lean sources, metadata and release links. Preserve earlier manuscripts, registered versions and evidence.

## 1. Fixed release identity

- Durable release tag **T**: `dosen-petric-v25-palomar-v3`.
- Candidate **C**: the full 40-character commit supplied in the delivery message and obtained by resolving `T^{commit}`. Require these two values to agree.
- Candidate commit subject: `Prepare v25 and fixed release tag for Palomar v3`.
- Existing registry identifier: `PALOMAR-2026-10-30-000014`.
- Registered v2 source: `5dbee39bea09539bd130f729e82636419f71f920`.
- Registered v1 source: `2e771844077fd8cebfbe365230f13d4dd13a75b1`.
- Superseded, unsubmitted v24 candidate: `c23fc48a109a08e74dae6ade9dcc9ee665b6f224`. Do not submit it.
- Repository-root project; Comparator: `comparator.json`; metadata: `formalization.yaml`.
- Lean toolchain: `leanprover/lean4:v4.35.0`; permitted axioms: `propext`, `Quot.sound`, `Classical.choice`.

The tag name is fixed before C is created. Source and claim-map URLs in C therefore name T, which must be created at C and never moved. There is no separate paper-first commit for this release, and no metadata-only second candidate. The delivery message supplies C because a commit cannot contain its own hash. A matching subject alone is insufficient to establish C.

The manuscript contains the anticipated version-specific v3 citation:
`https://palomar-registry.org/entry?id=PALOMAR-2026-10-30-000014&version=3`.
This is release-candidate content, not evidence of registration. Final publication is conditional on the service confirming **version 3 at C**. Do not replace it with a floating latest-version URL. If a different version or source is assigned, stop final publication and report the mismatch; never move T or silently substitute another commit.

Work in `/home/flengyel/src/Dosen-Petric-Maximality` in WSL2. Preserve unrelated edits and the stash. Use an isolated worktree when needed; do not reset or clean the author's checkout. Read `AGENTS.md`, `docs/CODEX_NEXT_SESSION.txt`, `docs/MANUSCRIPT_V25_REPORT.md`, `docs/PALOMAR_REQUIREMENTS.md`, `docs/PALOMAR_V2_REGISTRATION_REPORT.md`, and the retained v23/v24 review reports. Older v24 handoffs describe a superseded two-commit plan; this handoff governs this candidate.

## 2. Resolve and verify C; create T only if absent

Set `v25_expected_commit` to the exact full SHA in the delivery message. Do not derive this expected value from the tag or the current branch: it is the independent comparison value. Inspect `git status --short` before beginning. The preparation workflow may already have created the tag; verify it before attempting any creation.

The following Bash block fetches without forcing and creates the durable tag only when absent. It refuses conflicting local or remote tags. It must run with the expected SHA already set:

~~~bash
(
  set -euo pipefail
  cd /home/flengyel/src/Dosen-Petric-Maximality
  : "${v25_expected_commit:?Set this to the full candidate SHA supplied in the delivery message}"
  [[ "$v25_expected_commit" =~ ^[0-9a-f]{40}$ ]]
  v25_tag=dosen-petric-v25-palomar-v3
  v25_subject='Prepare v25 and fixed release tag for Palomar v3'
  git fetch origin --prune
  git cat-file -e "${v25_expected_commit}^{commit}"
  test "$(git show -s --format=%s "$v25_expected_commit")" = "$v25_subject"
  git merge-base --is-ancestor "$v25_expected_commit" origin/main

  if git show-ref --verify --quiet "refs/tags/$v25_tag"; then
    test "$(git rev-parse "${v25_tag}^{commit}")" = "$v25_expected_commit"
  fi

  if v25_remote_refs=$(git ls-remote --exit-code --tags origin \
      "refs/tags/$v25_tag" "refs/tags/${v25_tag}^{}"); then
    v25_remote_commit=$(printf '%s\n' "$v25_remote_refs" | \
      awk -v ref="refs/tags/$v25_tag" \
        '$2 == ref {direct = $1} $2 == ref "^{}" {peeled = $1} END {print peeled != "" ? peeled : direct}')
    test "$v25_remote_commit" = "$v25_expected_commit"
    git fetch origin "refs/tags/$v25_tag:refs/tags/$v25_tag"
  else
    v25_lookup_status=$?
    test "$v25_lookup_status" -eq 2
    if ! git show-ref --verify --quiet "refs/tags/$v25_tag"; then
      git tag "$v25_tag" "$v25_expected_commit"
    fi
    git push origin "refs/tags/$v25_tag:refs/tags/$v25_tag"
  fi

  test "$(git rev-parse "${v25_tag}^{commit}")" = "$v25_expected_commit"
  v25_remote_refs=$(git ls-remote --exit-code --tags origin \
    "refs/tags/$v25_tag" "refs/tags/${v25_tag}^{}")
  test "$(printf '%s\n' "$v25_remote_refs" | \
    awk -v ref="refs/tags/$v25_tag" \
      '$2 == ref {direct = $1} $2 == ref "^{}" {peeled = $1} END {print peeled != "" ? peeled : direct}')" = "$v25_expected_commit"
  git show --stat --oneline "$v25_expected_commit"
)
~~~

Any failing identity check stops this procedure. Do not add `--force`, delete an existing durable tag, or select a different candidate to make a check pass. If the delivery SHA is missing, recover it from the actual delivery record before proceeding. If T is already correct, do not recreate it.

Use the verified values for the remaining commands:

~~~bash
v25_repo=flengyel/Dosen-Petric-Maximality
v25_tag=dosen-petric-v25-palomar-v3
v25_candidate_commit=$(git rev-parse "${v25_tag}^{commit}")
test "$v25_candidate_commit" = "$v25_expected_commit"
v25_registered_commit=5dbee39bea09539bd130f729e82636419f71f920
~~~

Palomar intake takes C as a full commit SHA, not T or a branch name. Publishing T identifies the release candidate; it does not register a Palomar update.

## 3. Verify the single-commit snapshot

Inspect the files as committed at C, not uncommitted working copies. Confirm that the v25 source, PDF, bibliography, package, claim map and `formalization.yaml` are present together. The v25 date is 2 November 2026 in the author's local date; earlier UTC-dated records remain unchanged.

Check all 56 manuscript Lean source links and the current manuscript/source/claim-map references. Each current project link must target `blob/dosen-petric-v25-palomar-v3/…` or `tree/dosen-petric-v25-palomar-v3/…`. There must be no unresolved commit token, current-paper link to a paper-first commit, or floating `main` source link. Historical registration SHAs and original literature citations remain historical references. Confirm that tag resolution, metadata, release package and the anticipated v3 citation identify this same candidate.

Read `formalization.yaml` completely. Preserve its schema URL and version, classifications, five selected declaration names, namespace, modules, proof statuses and permitted axioms. `no_top_to_bot` is located at Appendix D.3. Retain “arrow term” as the technical expression and immutable Lean identifiers. Review provenance remains author-side AI-assisted source/manuscript review; it does not certify a fresh build or Palomar service review.

Verify that proof and verifier inputs are unchanged from registered v2:

~~~bash
git diff --exit-code "$v25_registered_commit" "$v25_candidate_commit" -- \
  DosenPetric DosenPetric.lean Challenge.lean Solution.lean Checks \
  comparator.json lean-toolchain lakefile.lean lakefile.toml lake-manifest.json
~~~

Stop to inspect any difference. This release does not authorize changing proofs, selected statements, dependency pins, definitions or permitted axioms. Reuse successful manuscript/package build evidence and proof checks when their exact inputs are unchanged. A newly assembled candidate still requires official full preflight at C. Preparation, a local build and a pushed tag are distinct from service verification or registration.

## 4. Recheck the live protocol and the expected successor

Read the current primary instructions before beginning the service transaction:

- <https://submit.palomar-registry.org/llms.txt>
- <https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md>
- <https://github.com/PalomarRegistry/PalomarPolicy/blob/main/docs/specification.md>
- <https://github.com/PalomarRegistry/PalomarSubmission>
- <https://data.palomar-registry.org/versions/PALOMAR-2026-10-30-000014.json>
- <https://data.palomar-registry.org/repositories/flengyel/dosen-petric-maximality.json>

The policy links are protocol references, not manuscript source links. Follow exact versioned entry paths returned by the service. Verify that v2 remains the current registered version and that C has not already been registered. If C is already registered as v3, verify that record and continue with readback instead of opening duplicate intake. If another update has changed the expected successor, stop and report the conflict before intake. Do not revise T to accommodate it.

Use the ordinary update route with the existing identifier. The Technical Maintainer correction route retains an old source commit and is not the route for this author-side update. Recheck accepted request fields and endpoint paths against the live instructions.

## 5. Official full preflight at C

The repository wrapper `.github/workflows/palomar-preflight.yml` accepts a `commit` input and calls the official reusable workflow in `full` mode, profile `palomar-standard-v1`, for root `comparator.json`. Verify that the reusable workflow is pinned to a full SHA and that `pipeline_commit` matches it. Recheck the upstream requirements before dispatch.

Use an already authenticated GitHub CLI. If a passing official full preflight for this exact C already exists, inspect and retain its evidence. Otherwise dispatch:

~~~bash
gh workflow run palomar-preflight.yml \
  --repo "$v25_repo" --ref "$v25_tag" \
  -f "commit=$v25_candidate_commit"
~~~

Identify the run by workflow, dispatch time and inputs, then record its ID and URL. Inspect its complete mechanical-report artifact. Require the exact C, root Comparator path, toolchain and selected declarations, a passing status and an empty blocking-errors list. Dispatch success or preparation-only mode is insufficient. A passing v2 or superseded v24 run does not certify C. Diagnose failed inputs or resource conditions before retrying.

## 6. Ordinary update intake and access proof

The author has authorized preparation of this concrete update. Reuse existing authorization for the named repository, exact delivered candidate, public metadata and responsible-author-or-maintainer relationship. Finish candidate verification and preflight before requesting any missing service-required agreement. Do not ask again for actions already authorized.

Use existing authenticated credentials. Check that repository tag creation/deletion and creation/deletion of a fresh secret gist are available before starting intake. Do not solicit passwords, automate browser sign-in or reuse a browser session as an authentication workaround. The access-proof window expires fifteen minutes after intake.

The documented intake payload is:

~~~bash
jq -n --arg commit "$v25_candidate_commit" '{
  repository: "flengyel/Dosen-Petric-Maximality",
  commit: $commit,
  comparator_config_path: "comparator.json",
  formalization_metadata_path: "formalization.yaml",
  authorization_relationship: "maintainer",
  existing_id: "PALOMAR-2026-10-30-000014"
}'
~~~

POST the JSON to `https://submit.palomar-registry.org/api/submit`. Keep the returned `pending_secret` private. Complete the current documented challenge procedure in the same sitting:

1. Create the temporary tag `refs/tags/palomar-verify-CHALLENGE` at C, using the exact returned challenge.
2. Create a fresh secret GitHub gist with `palomar.txt` containing the exact challenge. Respect the service's freshness requirement.
3. POST the returned `pending_secret` and new `gist_id` to `/api/verify`.
4. Retain `submission_id` and `access_token` privately.
5. Delete the temporary challenge tag and gist immediately after successful verification and confirm deletion.

Generate request JSON with a serializer. Do not concatenate challenge material into shell code or disclose secrets in traces. Store private responses and credentials only in ignored private staging. The durable tag T is not the challenge tag: never delete T during cleanup. Do not alter Palomar's archive preservation tags. If a required capability is missing, report it without starting an expiring partial intake or substituting a weaker authentication method.

## 7. Deliver the service review and register the approved bytes

Use the private bearer token with the documented submission-status and review endpoints. Honor retry limits: at most one status poll per minute during verification and one per five minutes while awaiting review or at review-ready, subject to stricter live instructions. Do not poll settled submissions or automatically resubmit an unknown outcome.

Deliver the exact returned review privately and retain its `review_sha256`. Explain that registration publishes the record, preservation evidence and archived review. Resolve requested corrections first. If corrections require changing C, stop this fixed-tag release; do not amend C or move T.

The service requires the author's decision on the delivered review before registration. Existing approval of the paper or intake is not approval of unseen review bytes. If the author has already authorized the exact returned review, proceed; otherwise present that concrete review and publication effect, identify the service's requirement, and await the decision. This is the final service approval boundary.

Once authorized, POST the exact returned digest to the registration endpoint prescribed by the current protocol:

~~~json
{"review_sha256": "EXACT_DIGEST_RETURNED_WITH_THE_APPROVED_REVIEW"}
~~~

Do not recompute a replacement digest or carry approval across changed review text. If the response assigns a version other than 3 or a source other than C, stop final publication, preserve the response as evidence and report the discrepancy. Never move T to match an unexpected result.

## 8. Verify v3 at C before final publication

After successful registration, verify the authenticated status, public version index, exact version-3 entry, repository identity, source commit and preservation receipt. Require all of the following:

- The public record is `PALOMAR-2026-10-30-000014`, **version 3**, with source **C**.
- The durable source tag still resolves to C, and its manuscript, PDF, source, metadata and claim-map links resolve to that same snapshot.
- The release-candidate BibTeX entry matches the confirmed version-specific record.
- Versions 1 and 2 and their archived evidence remain available.

Only then describe the v3 citation as confirmed and complete final publication of the v25 release. Do not issue another registry update solely to rewrite candidate-status prose inside C. Those statements accurately describe the snapshot at preparation; a later, separate registration report can record the outcome without changing C or T.

Record service results under `docs/` and dated provenance paths, excluding private tokens and unregistered private reviews. Copy final reports from committed bytes to `/mnt/c/Users/fleng/Downloads`, preserving differing existing copies, and verify SHA-256. Commit and push authorized subsequent evidence/report changes as separate history, leaving the v25 release tag and candidate unchanged.

Report the exact C, T and verified target; official preflight run URL; submission ID; confirmed registry version and exact public entry URL; and any remaining stage. Distinguish candidate publication, preflight, intake, service verification, delivered review, approval, registration and public readback. State which checks were reused. Do not claim registration from a pushed tag or prepared request.
