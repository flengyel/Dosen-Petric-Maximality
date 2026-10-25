# Author-side audit of the W6 construction instructions

## (A) Kill-shots / hard blockers

The reviewed object is `docs/CODEX_W6_CONSTRUCTION.md`, a construction and
implementation instruction for local Codex, anchored to main
`a17ec1b0b44c9fe7f5061bb35c2edfd1ded9ef90`. This is an author-side self-audit,
not independent peer review. The instruction asserts no new checked Lean result.

**A completed W6 or general Reducibility claim is unproved.** Anchor:
instruction §§1, 5–6; required source conclusion: the Reducibility Lemma on
printed p.250 and its right analogue on p.252. Failure mode: unproved.
Evidence: absence_in_text and structural_argument. The instruction specifies
new typed equality/rank obligations but supplies no compiled declarations for
them. In particular, the current logical context lemmas have the opposite
route variances from those needed in W6. Impact: neither addressed W6 nor
general Reducibility can be entered as complete. Severity: major for a proof
completion claim. Repair: implement and check the stated equalities, blocked
shapes, coordinates, ranks and addressed conclusions locally. This is an open
formalization obligation, not evidence of a manuscript or published error.

## (B) Major weaknesses

**The proposed families do not yet give arbitrary-input dispatch.** Anchor:
instruction §6; source p.250, quantification over every reducible subterm.
Failure mode if the construction were promoted to general Reducibility:
unsupported_generalization. Evidence: structural_argument. The left family is
built over the actual terminal `disjLLast` macro; native `disjL` has different
ancestry and is not itself that macro. The right family uses the existing
canonical last-retaining `BlockedR` patterns. Neither endpoint equality nor
categorical equality supplies the needed native/macro address correspondence.
Impact: local families do not discharge the arbitrary-address general
producer, outside-site transport or Blocked-w. Severity: major for general
completion. Repair: complete the specified transport and producer dispatch
without strengthening the final hypotheses. The instruction preserves this
obligation explicitly.

No additional confirmed obstruction to the six proposed local constructions
was found in the inspected definitions. The checks below concern their
mathematical design, not elaboration of a Lean implementation.

## (C) Minor issues

The instruction defines the route-arrow shorthand for selections and blocks
as well as routes. This avoids using s× or dR+ without a typed interpretation.
Singleton-aware contraction is specified on the actual extended/prefixed
contexts; no arity-zero or arity-one contraction constructor is introduced.
No additional local exposition defect is recorded.

## (D) Cross-section consistency failures

The following checks found no conflicting mathematical requirement:

| Claim and anchor | Derivation and scope |
|---|---|
| Left endpoint and blockedness, §2 | With K=X++C::Y and L=Z++C::T, the three gaps `[X,Y++Z,T]` and empty tail have upper context `(K++L)++[C]` and lower context `(X++Y++Z++T)++[C]`. This matches `disjunctionBoth` after list transports. |
| Left ranks, §2 | Each selected parametric path in `disjLLast` traverses three nodes; the fresh C traverses its introduction and final exchange. Summing every selected copy plus the outer contraction gives old `Sp+Sq+3(n+m)+3` and new `Sp+Sq+δ(n)+δ(m)+9`. |
| Right endpoint and blockedness, §4 | `more (p.chain q)` retains the last q position in `p.erased++L`. Gaps `[[],X,Y++Z]` with tail T select the fresh head, retained p and retained q, matching `conjunctionBoth`. |
| Right ranks, §4 | Native conjR contributes one node per parametric path and one fresh leaf. Old rank is `Sp+Sq+n+m+2`; new rank is `Sp+Sq+δ(n)+δ(m)+4`. The left macro's extra exchanges are not copied into this calculation. |
| One selected premise, §§3–4 | The left old/new ranks are `S+3k+3` and `S+δ(k)+6`; the right ranks are `S+k+2` and `S+δ(k)+3`. Fixed positions in the other premise remain separate, even at equal formula labels. |
| Boundary arities, §§2–4 | δ(1)=0; δ(k)=1 for k≥2. The inequality δ(k)+1≤k proves all root nonincrease bounds. A blocked new root permits equality of root ranks. Singleton old patterns are already blocked and cannot satisfy the reducible-input hypothesis. |
| Categorical equalities, §§2 and 4 | Left products factor as `d×;R×`, right coproducts as `R_R+;dR+`. The stated naturality inputs have the corresponding directions and folded endpoints. Component identities are required; occurrence equality is never reflected. |
| Full descendant quantifier, §5 | Existing `descendants_left/right` reject the blocked root and use strict rank descent on every proper address, together with entry uniqueness from hr. This includes surviving contractions; no extra caller hypothesis is specified. |

The instruction changes no source equation, rank, blockedness or reducibility
definition. It preserves the right-W4 repair and all settled manuscript
decisions. No claim of nonthinness, coherence or maximality is inferred from
these rank calculations.

## (E) Acceptance conditions, non-negotiable

1. Check all six old/new constructions at their exact endpoints, with complete
   selected lists and common retained positions; failure prevents a W6 claim.
2. Prove both missing naturality directions and the route factorizations in
   Reduced.Hom from the existing equations; an assumed equality or coherence
   premise is not an implementation.
3. Derive the full macro/native rank equations, including singleton cases and
   equal-label fixed positions; retain a counterexample if a proposed equation
   fails and repair the instruction rather than the underlying definitions.
4. Check every addressed theorem with the complete descendant quantifier and
   only the original ReducibleL/R input; root-rank comparisons alone do not
   suffice.
5. Complete general dispatch and the later outside-site/multiset obligations
   before promoting local W6 to general Reducibility or Blocked-w. Their
   absence rejects those completion claims, not the scoped instruction.
6. Apply local verification to the actual implementation and preserve exact
   checked/committed source evidence before marking new declarations proved.

## (F) Not checked / uncertainty log

Read the governing records and the named existing source interfaces; consulted
the hash-verified book at printed pp.248–253 and rendered p.252. The complete
v6 TeX was read for continuity, but its mathematics and bibliography were not
independently re-audited here. No new manuscript defect is alleged.

No W6 implementation was compiled or kernel checked. No source build, audit,
negative control, Palomar check or submission was performed. The inaccessible
WSL working tree, stash, SSH refs and Windows delivery are not verified.

Strongest confirmed blocker to completion: the new W6 declarations and general
producer are still absent from the reviewed source. Strongest suspected,
unconfirmed difficulty: the native/source-macro ancestry comparison may need
additional local cases; no counterexample to the unchanged target is known.
Most important unchecked item: the actual Lean implementation of the two new
categorical naturality equalities and six addressed families. Recommendation
does not depend on an unavailable mathematical source. Final recommendation:
reject a completed-proof claim; retain this scoped construction instruction
for local implementation and subsequent review.
