# Došen–Petrić maximality in Lean

Development for Florian Lengyel's *Maximality of the Došen–Petrić Boolean
Category*, manuscript v4. The target is maximality of the free zero-identity
Boolean category under substitution congruences.

The WSL2 development uses pinned Lean 4.35.0 with an Init-only dependency
closure. Conditional contextual collapse, signed-literal isolation,
substitution transport and relative maximality are proved under explicit
inputs. A generated nonthin structural model instantiates every §5 interface
field; it is separate from the actual source presentation.

The September 2007 presentation now has typed arrow syntax, a generated
syntactic quotient category, structural and zero-identity bridges,
substitution, double negation, normalization and a well-defined tagged
occurrence assignment with global signed-label preservation. Signed-literal
reduction is surjective on normal-form hom-sets. Contextual and common atomic
factorizations, complete occurrence support and the positive zero/union algebra
are proved. These constructions do not establish occurrence faithfulness.

Typed positive Gentzen syntax and existential representation with cuts,
Atomic-k thinning atomization, finite ancestor clusters/rank, and the two
opposite-side thinning and two opposite-side exchange instances of W1 compile.
The opposite-side contraction commutation also compiles as one pair with two
directed rank comparisons: each lowers its targeted side and raises the other.
The sum of these endpoint ranks is not a general decreasing measure.
Both opposite-side unary logical commutations (disjR/conjL) also compile, with
full selected-copy rank losses and introduced whole-formula principal ranks
2→1. These complete the specified opposite-side unary W1 families; same-side
exchange/contraction/logical parametric cases and binary rules remain separate.
Same-side thinning through contraction now compiles at fixed interior gaps and
terminal tails, with both duals, explicit positional routing and complete ordered
selected-copy transport even when the inserted formula equals the contracted
formula. Exact local rank losses and predicate/tagged-relation preservation
are proved; these instances do not establish all-site reducibility.
The current stage is the remaining local contraction transformations toward
cut elimination. General W1, W2–W6, blocked-contraction transformations,
Reducibility, cut elimination, the positive coherence inputs, PositiveCoherence,
Reduced.Faithful, Boolean Coherence and unconditional maximality remain open.
See [validation](docs/VALIDATION.md) for the maintained audited declaration
count, commands, evidence and limits of the local checks.

## WSL2 setup

The intended directory is `/home/flengyel/src/Dosen-Petric-Maximality`, on the
WSL2 Linux filesystem. With GitHub SSH authentication configured and Elan installed:

```bash
mkdir -p /home/flengyel/src
git clone git@github.com:flengyel/Dosen-Petric-Maximality.git /home/flengyel/src/Dosen-Petric-Maximality
cd /home/flengyel/src/Dosen-Petric-Maximality
bash scripts/setup-wsl.sh
```

If that directory already exists, inspect its Git status and origin before
updating it. See [WSL2 instructions](docs/WSL2_SETUP.md) for prerequisites.
The setup installs only the pinned project toolchain and runs verification;
it does not change Elan's global default. Local build and audit outcomes are recorded in validation.

Initial modules use Lean core only. The matching Mathlib release is recorded
at full commit `56a005855ea17e0b0958f73ec801ae140b0a1679`; it is not an active
dependency. The committed Lake manifest therefore has no dependency packages.

## Proof scope and continuation

1. Contextual collapse relative to explicit structural and faithful-interpretation data.
2. Maximality relative to explicit coherence, normalization, presentation, and substitution inputs.
3. Maximality for the actual Došen–Petrić presentation after those inputs are established.

The conditional theorems do not complete the intended-presentation milestone
gates. Many syntactic bridges above are constructed, while coherence and
remaining congruence/substitution interfaces are still required. Coherence
applies in the original category; zero arrows require a witness that the
hom-set is inhabited.
The [statement map](docs/MANUSCRIPT_STATEMENTS.md) and
[coverage map](docs/MANUSCRIPT_COVERAGE.md) record the precise boundary.
Use [the next-session prompt](docs/CODEX_NEXT_SESSION.txt) to continue in WSL2.

The unchanged v4 [TeX](manuscript/Maximality_of_the_Dosen_Petric_Boolean_Category_v4.tex)
and [PDF](manuscript/Maximality_of_the_Dosen_Petric_Boolean_Category_v4.pdf)
are preserved with [SHA-256 checksums](manuscript/SHA256SUMS).
The [literature comparison](docs/LITERATURE_REVIEW.md) is bounded and makes no
exhaustive priority claim. The current [author-side hostile review](docs/reviews/GENTZEN_W1_SAME_SIDE_THINNING_HOSTILE.md)
and [mathematical-writing review](docs/reviews/GENTZEN_W1_SAME_SIDE_THINNING_WRITING.md)
cover the fixed-position same-side thinning checkpoint and its scope; they are not independent
certification. The [same-side thinning report](docs/GENTZEN_W1_SAME_SIDE_THINNING_REPORT.md),
[preceding logical report](docs/GENTZEN_W1_LOGICAL_REPORT.md),
[preceding contraction report](docs/GENTZEN_W1_CONTRACTION_REPORT.md),
[contraction review](docs/reviews/GENTZEN_W1_CONTRACTION_HOSTILE.md),
[preceding exchange report](docs/GENTZEN_W1_EXCHANGE_REPORT.md),
[exchange review](docs/reviews/GENTZEN_W1_EXCHANGE_HOSTILE.md),
[preceding thinning review](docs/reviews/GENTZEN_W1_THINNING_HOSTILE.md),
[historical contextual-collapse review](docs/reviews/CONTEXTUAL_COLLAPSE_HOSTILE.md)
and [initial review](docs/REVIEW.md) remain available.

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
