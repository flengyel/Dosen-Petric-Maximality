# Došen–Petrić maximality in Lean

Development for Florian Lengyel's *Maximality of the Došen–Petrić Boolean
Category*, manuscript v4. The target is maximality of the free zero-identity
Boolean category under substitution congruences.

The preliminary development builds with Lean 4.35.0. It proves zero-identity
lemmas, the tagged occurrence bijection for substitution, and relation
calculations used by the contextual-collapse argument. The axiom audit passes
for 176 imported project declarations. Contextual collapse, occurrence
isolation, and maximality remain open. See [validation](docs/VALIDATION.md).

## WSL2 setup

The intended directory is `/home/flengyel/src/Dosen-Petric-Maximality`, on the
WSL2 Linux filesystem. With GitHub CLI authenticated and Elan installed:

```bash
mkdir -p /home/flengyel/src
gh repo clone flengyel/Dosen-Petric-Maximality /home/flengyel/src/Dosen-Petric-Maximality
cd /home/flengyel/src/Dosen-Petric-Maximality
bash scripts/setup-wsl.sh
```

If that directory already exists, inspect its Git status and origin before
updating it. See [WSL2 instructions](docs/WSL2_SETUP.md) for prerequisites.
The setup installs only the pinned project toolchain and runs verification;
it does not change Elan's global default. Preparation and CI ran remotely;
validation on the WSL2 machine is still pending.

Initial modules use Lean core only. The matching Mathlib release is recorded
at full commit `56a005855ea17e0b0958f73ec801ae140b0a1679`; it is not an active
dependency. The committed Lake manifest therefore has no dependency packages.

## Proof scope and continuation

1. Contextual collapse relative to explicit structural and faithful-interpretation data.
2. Maximality relative to explicit coherence, normalization, presentation, and substitution inputs.
3. Maximality for the actual Došen–Petrić presentation after those inputs are established.

No milestone is completed by the preliminary lemmas. Coherence applies in the
original category; zero arrows require a witness that the hom-set is inhabited.
The [statement map](docs/MANUSCRIPT_STATEMENTS.md) and
[coverage map](docs/MANUSCRIPT_COVERAGE.md) record the precise boundary.
Use [the next-session prompt](docs/CODEX_NEXT_SESSION.txt) to continue in WSL2.

The unchanged v4 [TeX](manuscript/Maximality_of_the_Dosen_Petric_Boolean_Category_v4.tex)
and [PDF](manuscript/Maximality_of_the_Dosen_Petric_Boolean_Category_v4.pdf)
are preserved with [SHA-256 checksums](manuscript/SHA256SUMS).
The [literature comparison](docs/LITERATURE_REVIEW.md) is bounded and makes no
exhaustive priority claim. The [automated review](docs/REVIEW.md) records the
remaining mathematical obligations.

## Verification and Palomar

Run `bash scripts/verify.sh`. CI uses the hash-checked official Lean release,
a strict build, source screening, and transitive axiom collection. Evidence
and its limitations are in [validation](docs/VALIDATION.md).

The [Palomar requirements](docs/PALOMAR_REQUIREMENTS.md) adapt the
FailureOfComposition procedure to the current toolchain and kernel policy.
Upstream policy snapshots and exact commits are in `provenance/`.
`bash scripts/fetch-palomar.sh` fetches the pinned verifier source for inspection.
Comparator packaging, independent kernel replay, and registry verification
remain to be implemented for a substantive theorem.

The repository is private. Public release, license selection, and registry
submission are later decisions. No submission has been made.
