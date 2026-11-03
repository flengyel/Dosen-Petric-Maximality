# Codex continuation: v24 paper and Palomar update

Implement the remaining repository and Palomar synchronization for **flengyel/Dosen-Petric-Maximality**. The v24 manuscript corrections are complete in the incoming paper commit. This task continues that work; it does not reopen the completed mathematical formalization.

## Source identities and preserved records

- Paper snapshot: **59e20c7b907d97a4e76e89b69adb560383e458ba**.
- Final metadata/submission candidate: the unique commit with the final-candidate subject below; resolve its full SHA as specified in Section 1.
- Paper-commit subject: **Revise maximality manuscript to v24 after joint review**.
- Final-candidate subject: **Synchronize v24 Palomar metadata and Codex handoff**.
- Existing permanent result: **PALOMAR-2026-10-30-000014**.
- Registered v2 source: **5dbee39bea09539bd130f729e82636419f71f920**.
- Registered v1 source: **2e771844077fd8cebfbe365230f13d4dd13a75b1**.
- Repository-root project; Comparator path **comparator.json**; metadata path **formalization.yaml**.
- Lean toolchain: **leanprover/lean4:v4.35.0**.
- Permitted axioms remain **propext, Quot.sound, Classical.choice**.

The paper SHA is pinned above. This file is included in the final candidate, so its own commit is resolved from the exact subject rather than written self-referentially. The delivery message also supplies that full SHA. Require a unique match and verify the remote ancestry. Do not pass a branch, abbreviated SHA, or tag to Palomar.

Work under /home/flengyel/src/Dosen-Petric-Maximality in WSL2. Preserve unrelated working-tree changes, the stash, earlier manuscripts and packages, both proof routes, and existing registry evidence. Use an isolated worktree when necessary; do not reset or clean the author's checkout.

## 1. Inspect the incoming commits

Read AGENTS.md, docs/CODEX_NEXT_SESSION.txt, docs/MANUSCRIPT_V24_REPORT.md, docs/reviews/V23_JOINT_HOSTILE_WRITING_REVIEW_2026-11-03.md, docs/PALOMAR_REQUIREMENTS.md, and docs/PALOMAR_V2_REGISTRATION_REPORT.md.

Fetch and inspect before making any changes:

~~~bash
cd /home/flengyel/src/Dosen-Petric-Maximality
git status --short
git fetch origin --prune
git log origin/main --format='%H %s' --grep='^Revise maximality manuscript to v24 after joint review$'
git log origin/main --format='%H %s' --grep='^Synchronize v24 Palomar metadata and Codex handoff$'
~~~

Use the exact supplied/resolved commits as task-specific variables:

~~~bash
v24_repo=flengyel/Dosen-Petric-Maximality
v24_paper_commit=59e20c7b907d97a4e76e89b69adb560383e458ba
mapfile -t v24_candidates < <(git log origin/main --format='%H' \
  --grep='^Synchronize v24 Palomar metadata and Codex handoff$')
if [ "${#v24_candidates[@]}" -ne 1 ]; then
  printf '%s\n' 'Expected exactly one v24 candidate; inspect the supplied commit before proceeding.' >&2
  return 1 2>/dev/null || exit 1
fi
v24_candidate_commit=${v24_candidates[0]}
v24_registered_commit=5dbee39bea09539bd130f729e82636419f71f920
~~~

Require both new values to be 40 lowercase hexadecimal characters and resolvable commits. Verify that the paper commit is an ancestor of the candidate and that the candidate is available from the remote:

~~~bash
git cat-file -e "$v24_paper_commit^{commit}"
git cat-file -e "$v24_candidate_commit^{commit}"
git merge-base --is-ancestor "$v24_paper_commit" "$v24_candidate_commit"
git merge-base --is-ancestor "$v24_candidate_commit" origin/main
git show --stat --oneline "$v24_paper_commit"
git show --stat --oneline "$v24_candidate_commit"
~~~

A later documentation commit on main does not silently replace the submission candidate.

The paper changes are local exposition corrections: explicit substitution closure in Appendix D.4; the positive-normal-form explanation; the factorization wording; the normal-form hom-set footnote; introductory pointers; the equivalence reference; contextual “morphism” terminology; and the two accepted economy/navigation edits. Preserve the technical expression “arrow term” and immutable Lean identifiers. Do not insert this account into mathematical exposition.

## 2. Verify the metadata and preservation boundary

Read the candidate's formalization.yaml in full. Its manuscript source and broader-correspondence links must point to the **paper snapshot**, not an unresolved token or mutable main branch. Check the title, abstract/description, provenance, source locations, alignment statements, and v24 references against the delivered paper. Keep the five selected theorem names and their mathematical content unchanged.

The paper still cites the completed v2 registry entry. Preparation of a new candidate is not registration of v3. Do not insert a future registry version or a fabricated BibTeX entry into the paper.

Confirm that the proof and verifier inputs are unchanged from the registered source:

~~~bash
git diff --exit-code "$v24_registered_commit" "$v24_candidate_commit" -- \
  DosenPetric DosenPetric.lean Challenge.lean Solution.lean Checks \
  comparator.json lean-toolchain lakefile.lean lake-manifest.json
~~~

Inspect any difference before proceeding. A documentation or metadata revision does not authorize changing proofs, selected statements, definitions, dependency pins, or permitted axioms.

Reuse the delivered manuscript/package build evidence and the existing local proof verification where their exact inputs are unchanged. Do not repeat successful full builds merely because a new documentation commit exists. A new candidate nevertheless needs its own official full mechanical preflight under the service's exact-commit procedure. Reuse a completed passing preflight for this exact candidate if one already exists.

Review the prospective public metadata and the new manuscript references with the mathematical-writing and hostile-referee instructions. Keep those reports outside the manuscript. Verify that placeholder tokens are absent from the submitted formalization metadata.

## 3. Release tag and registry tags are different

No durable release-tag name was recovered from the earlier chat or current repository records. Do not claim that one was recovered or create a guessed tag under that description. If the author supplies the previously agreed release tag, create it at the exact designated candidate and push it without moving or overwriting any existing tag. If it exists at another commit, report the conflict; do not force it.

A source-repository release tag identifies a snapshot. It does **not** automatically update Palomar. The repository currently has no tag-triggered registry-update workflow.

The agent authentication tag has a different, service-defined name:
**refs/tags/palomar-verify-CHALLENGE**. CHALLENGE is returned by the new intake; it cannot be chosen in advance. This tag is temporary and must be deleted after verification.

Palomar's immutable preservation tags live in its archive fork. Do not create, move, or delete them. Existing v2 preservation is:

- Archive repository: PalomarArchive/flengyel--Dosen-Petric-Maximality--63db84754d7f
- Ref: refs/tags/palomar/PALOMAR-2026-10-30-000014-v2/5dbee39bea09539bd130f729e82636419f71f920

## 4. Recheck the live protocol and registry identity

Read the current primary sources before intake:

- https://submit.palomar-registry.org/llms.txt
- https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md
- https://github.com/PalomarRegistry/PalomarPolicy/blob/main/docs/specification.md
- https://github.com/PalomarRegistry/PalomarSubmission

At preparation on 3 November 2026, the upstream heads still matched:

- PalomarSubmission: **14aa8d6b3c2f14a8540605e37144560b9a00e7e7**
- PalomarPolicy: **28bd48b9b71bbb2a82c718ce761d5a4220ef8e60**

These observations do not replace checking for subsequent changes. The repository's preflight wrapper pins the first revision in both its reusable-workflow reference and pipeline_commit.

Read the public version index and its returned active entry:

- https://data.palomar-registry.org/versions/PALOMAR-2026-10-30-000014.json
- https://data.palomar-registry.org/repositories/flengyel/dosen-petric-maximality.json

Follow the returned exact entry/reference paths. Do not add cache-busting query parameters. If v2 remains the latest active record, the expected ordinary successor is v3; do not assume that number without checking. Check that the candidate commit is absent from the registration identity's already registered commits. The identity digest is SHA-256 of the UTF-8 concatenation:

~~~text
lowercase_repository + NUL + project_path_or_empty + NUL + comparator_config_path
~~~

Use the ordinary update route under the existing identifier. The Technical Maintainer correction route is for separately allowlisted Palomar maintainers and retains the old source commit; it is not an author-side shortcut for this update.

## 5. Exact-candidate official full preflight

The existing wrapper .github/workflows/palomar-preflight.yml accepts one workflow-dispatch input, commit. It calls the pinned official workflow with mode full, profile palomar-standard-v1, root comparator.json, and the responsible-author-or-maintainer relationship.

With an already authenticated GitHub CLI and sufficient Actions permission:

~~~bash
gh workflow run palomar-preflight.yml \
  --repo "$v24_repo" --ref main \
  -f "commit=$v24_candidate_commit"
~~~

Identify the newly dispatched run from its workflow, dispatch time and inputs. Do not assume that the workflow run's headSha equals the separately supplied candidate input. Record the run ID and URL. Obtain and read its complete mechanical-report artifact; check that it names the exact candidate, Comparator path, toolchain and selected declarations. Require status pass and an empty blocking-errors list. Preparation-only mode or a bare Comparator success is insufficient.

The wrapper's successful dispatch does not imply preflight success. A passing preflight is not service verification, review, or registration. If an unchanged-input invocation already passed, retain its evidence and do not rerun it. For failed input/profile/resource conditions, follow the reported diagnosis rather than repeatedly submitting the same failed call.

## 6. Ordinary update intake and temporary access proof

Before calling intake, check that existing session authorization covers the concrete repository, full candidate commit, root Comparator path, public metadata and Florian Lengyel's responsible-author-or-maintainer relationship. Reuse that authorization when it does. If the exact candidate or public proposal has not yet been presented, finish the concrete candidate and preflight first, then present those values together for the service-required agreement. Do not ask for repeated approval of already authorized preparation.

Use existing authenticated credentials. Do not solicit passwords, create replacement credentials, automate browser sign-in, or repurpose a browser session as authorization. Check that both repository ref creation and creation/deletion of a fresh secret gist are available **before** starting intake.

The live documented intake request has this shape:

~~~bash
jq -n --arg commit "$v24_candidate_commit" '{
  repository: "flengyel/Dosen-Petric-Maximality",
  commit: $commit,
  comparator_config_path: "comparator.json",
  formalization_metadata_path: "formalization.yaml",
  authorization_relationship: "maintainer",
  existing_id: "PALOMAR-2026-10-30-000014"
}'
~~~

POST the generated JSON to https://submit.palomar-registry.org/api/submit. Keep the returned pending_secret private; obtain the exact challenge from the response.

Complete the documented proof in the same sitting. Intake expires after fifteen minutes, so do not begin it before the required tools and agreement are ready:

1. Create refs/tags/palomar-verify-CHALLENGE at the exact candidate using the returned challenge.
2. Create a fresh **secret** GitHub gist containing a file named palomar.txt whose complete content is that challenge. A public or stale gist is invalid.
3. POST the exact returned pending_secret and new gist_id to /api/verify.
4. Retain submission_id and access_token privately.
5. Delete the temporary tag and gist immediately after successful verification and confirm their deletion.

The official GitHub command shapes are:

~~~bash
gh api -X POST "repos/$v24_repo/git/refs" \
  -f "ref=refs/tags/palomar-verify-$v24_challenge" \
  -f "sha=$v24_candidate_commit"
~~~

Create the gist by sending a JSON file or structured stdin object to gh api -X POST gists --input -, with public set to false and files.palomar.txt.content set to the returned challenge. Generate JSON with a JSON serializer; do not concatenate untrusted values into shell code.

Cleanup uses:

~~~bash
gh api -X DELETE "repos/$v24_repo/git/refs/tags/palomar-verify-$v24_challenge"
gh api -X DELETE "gists/$v24_gist_id"
~~~

The pending secret, access token, private review response and consent digest belong in ignored private staging. Never place them in a public report, commit, shell trace, or copied general-purpose log. If tag or gist permissions are unavailable, do not substitute a weaker authentication scheme; report the exact capability that is missing.

## 7. Monitor, deliver the review, then register only the approved review

Use Authorization: Bearer with the private access token for:

- GET /api/submission
- GET /api/review
- POST /withdraw, only if withdrawal is intended.

Poll at most once a minute during running verification and once every five minutes while awaiting review or at review-ready. Honor cooldowns, terminal states and any retry-after instruction. Do not poll settled submissions or automatically resubmit an explicitly unknown outcome.

When the review is ready, deliver its exact returned text privately, retain the returned review_sha256, and explain that registration publishes the record, source-preservation evidence and archived review. Resolve any requested correction before proceeding. Approval of the paper, the candidate or intake does not supply a decision concerning an unseen service review.

The live service explicitly requires a decision on the delivered review before POST /register. If the author has already authorized those exact review bytes, proceed without asking again. Otherwise this is the final approval boundary: present the exact review and publication effect, identify the service requirement, and wait for that decision.

Authorized registration sends:

~~~json
{"review_sha256": "EXACT_DIGEST_RETURNED_WITH_THE_APPROVED_REVIEW"}
~~~

POST it to /register with the same private authorization header. Do not manufacture or recompute a substitute digest. If the review changes, its earlier approval does not bind the replacement.

## 8. Verify publication and finish synchronization

After registration succeeds, verify the authenticated status and the public version index, entry, repository identity, source commit and preservation receipt. Confirm that the public source reference names the candidate and that the descriptive metadata points to the v24 paper snapshot. Preserve versions 1 and 2 and all earlier evidence.

Keep these statuses separate in the final report: candidate committed/pushed; exact-candidate preflight; intake; service verification; delivered review; registration decision; registered public version; readback. Do not report a registry update from a pushed tag or a prepared request.

The paper's v2 citation remains accurate until the successor is registered. Updating that citation or any published manuscript text afterward requires the next manuscript number under AGENTS.md; do not overwrite v24. Use the actual new registry record and its supplied bibliography data, preserving earlier BibTeX entries. Synchronize the resulting active manuscript/package links and metadata in the same subsequent revision. Do not initiate a further registry version merely to remove this expected one-step citation dependency.

Retain reports under docs/ and evidence under a dated provenance directory. Copy final reports from committed bytes to /mnt/c/Users/fleng/Downloads, preserving differing existing copies, and verify SHA-256. Commit and push authorized documentation/evidence changes; verify the remote ref before reporting completion. Keep private service artifacts excluded.

## Completion report

Report the exact paper commit, candidate commit, any authorized durable release tag and its target, official run URL, submission ID, final registry version and public entry URL, or the precise remaining stage. State which checks were reused and which ran for the candidate. Identify repository and Downloads report paths. Do not claim a durable tag, registry update, successful check, or citation revision that was not completed.

