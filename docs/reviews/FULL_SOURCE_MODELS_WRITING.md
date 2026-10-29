# Local mathematical-writing review: model corollary

Governing source: Knuth, Larrabee and Roberts, *Mathematical Writing*, complete
cached PDF in `.codex-work/references/knuth-mathematical-writing-mit-9bf404c2.pdf`,
SHA-256 `9bf404c2c75633a1f39aae97af0b2e9335ce6d83cf386c84906654589b4e82e6`.
The complete-source workflow and §1 items 5, 10–15, 17 and §§4–5 were reapplied.
This is a local author-side prose/correspondence review, not an external review.

The argument order is: define full primitive semantics; prove equation closure
and quotient descent; construct full interpretations at each valuation; prove
composition with substitution and evaluation correspondence; instantiate the
actual source model; prove universal agreement is a full congruence; apply
maximality and the native product laws. The report follows that dependency order.
Definitions precede their theorem uses. Object, source-variable and hom universes
are independent. Heterogeneous equality is explained as retaining actual object
identifications, rather than treating endpoints as silently identical.

| Prose claim | Check/revision | Result |
| --- | --- | --- |
| Full model | Every primitive family and Equation schema, with source instantiation | No “model” label for an incomplete tensor fragment. |
| All interpretations versus valuations | Construct canonical family and prove hom_evaluation/iff_valuations | No assumed initiality or quotient bridge. |
| Substitution congruence | Precomposition gives fragment closure; proved dichotomy supplies full closure | Fixed-kernel closure is never asserted. |
| Preorder target | Native pair and both beta laws, all existing hom-sets | No image-only or surjectivity shorthand. |
| Negation | Full raw macro, not a new primitive or an unspecified target functor | Source/target semantics are stated explicitly. |
| Scope and verification | Process facts in reports; mathematical claim tied to declarations | No whole-paper certification or unavailable review claim. |

The strongest exposition risk was compressing the full congruence argument to
“functoriality”. The report instead identifies the independent fragment-dichotomy
proof and its two equality/total cases. The chosen source variable and constant
valuation explain the nonempty hypothesis before the native pairing step.
Empty hom-sets and existing-arrow zeros retain their stated meanings.

No manuscript prose was changed for this milestone. All nine manuscript blobs,
prior versions, ten diagrams and Appendix A references are preserved; unchanged
TeX was not rebuilt. FP-SCOPE-20261029 remains a coordinated final status refresh,
not a mathematical theorem repair. The remaining action/profile/ordinal claims
are explicitly open. Existing typed diagrams require no new diagram at this step.

Recommendation: the local report and claim map are precise enough to accept with
the recorded local checks. Independent review and the full-paper endpoint remain
separate statuses.
