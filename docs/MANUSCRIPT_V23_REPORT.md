# Manuscript v23: implemented review and validation

2 November 2026. Base: v22 at 5b515365f5d5164ba65c91ab3571fd2f475a0b66.
The author requested direct implementation of the reviewed changes. V23 is
23 pages; v22 and every earlier release remain.

- [Revised PDF](../manuscript/Maximality_of_the_Dosen_Petric_Boolean_Category_v23.pdf)
- [Revised TeX](../manuscript/Maximality_of_the_Dosen_Petric_Boolean_Category_v23.tex)
- [Complete before/after TeX diff](../provenance/manuscript-v23-review-20261102/v22-to-v23.diff)
- [arXiv source archive](../submission/arxiv-v23/Dosen-Petric-Maximality-v23-arxiv-source.tar.gz)
- [Implementation review](reviews/V23_IMPLEMENTATION_REVIEW_2026-11-02.md)
- [Original full review and rewrites](reviews/V22_REVIEW_AND_REWRITES_2026-11-02.md)
- [Validation record](../provenance/manuscript-v23-review-20261102/validation.json)

## Changes

The introduction follows the argument and moves four detailed literature
comparisons to their points of use. The unused proof-net paragraph is removed.
The proof outline explicitly includes substitution and double-negation transport.
The abstract loses the earlier repeated “also”; its accepted Lean sentence remains.
Section 6 is titled “A second proof and the Lean formalization”.
Appendix C identifies the typos in the cut-elimination argument used for
Došen–Petrić's Boolean Coherence proof and gives both strict rank inequalities.
“Raw terms” becomes “arrow terms”. The empty-union sentence uses the zero arrow
on a nonempty hom-set. Appendix D.5 names the equations used for the union-zero
law. The Notation citation is pinned to the inspected source commit.

## Preservation and checks

Seven numbered statements, six proof environments, twelve numbered equations,
77 displayed formulas, thirteen diagrams, 34 labels and all 56 Lean hyperlink
occurrences are byte-identical to v22. The 49 destinations and supplied Palomar
v2 BibTeX are unchanged. All earlier release files and Lean/frozen inputs are
outside this release's write set and retained by the base-tree update.

The source and independently extracted archive compile successfully to matching
23-page text, coordinates and bibliography. All pages were visually inspected.
The final log has one underfull bibliography paragraph from the pinned URL;
the line wraps inside the margins. There are no unresolved citations/references,
overfull boxes or duplicate destinations. No formal-proof defect was established.
No Lean build/kernel replay, Palomar registration or arXiv upload was performed.

## Delivery

The new files and reports are retained in the repository and provided directly
to the author. The Windows/WSL filesystem is unavailable in this environment,
so no new Downloads copy or receipt is claimed. Earlier delivery receipts remain.

## Final replacement text

The full diff above shows every change. The two largest replacements follow
so the exact published prose can be reviewed without reconstructing the diff.

### Introduction

```latex
We prove that the freely generated zero-identity Boolean category of
Do\v{s}en and Petri\'c over a nonempty set of propositional variables
is maximal. Adding any equation between parallel arrows that does
not follow from its defining equations, and closing under the arrow
operations and uniform formula substitution, collapses the category
to a preorder. This disproves Do\v{s}en and Petri\'c's conjecture that the category
is not maximal \cite[\S14.2, p.~322]{DP}. Before adjoining the equation, the
two projections $p\wedge p\to p$ are distinct for every
propositional variable $p$.

The proof reduces an added equation to equality of the product
projections, as in the maximality theorem for cartesian categories
\cite[\S5]{DPCartesian}. Boolean Coherence supplies a pair of
variable occurrences belonging to one arrow's relation and not the
other. Precomposition and postcomposition isolate this pair and
give the equation of \cite[\S9.7, pp.~215--216]{DP}.
Uniform substitution and the double-negation isomorphism then give
this equation for every formula.
The two isomorphisms listed in \cite[\S12.5, p.~294]{DP}
give equality of the product projections. Sections~\ref{sec:isolation}
and~\ref{sec:collapse} present this proof; Section~\ref{sec:formalization}
gives a second proof using mix. The proof of
\cite[Lemma~7]{DPIsomorphic} also supplies the two isomorphisms.

Other notions of Boolean category need not make conjunction and
disjunction categorical products and coproducts. Free categories constructed from classical proof nets
are studied in \cite[Theorem~3.5.4]{LSFree}, equations on monoid
and comonoid structures in $*$-autonomous categories in
\cite{Strassburger}, and inequalities interpreting cut reduction
in \cite{FP}. Section~\ref{sec:category} compares the negation
equation of \cite{FP} with the zero-identity equation used here.

We use the occurrence coordinates of \cite[\S9]{Notation}:
occurrences form tagged disjoint unions, and substitution replaces
each occurrence by a block. Section~\ref{sec:occurrences} defines
these coordinates; Appendix~\ref{app:substitution} proves their
correspondence with the finite-ordinal substitution formula of
Do\v{s}en and Petri\'c. Section~\ref{sec:formalization} and
Appendix~\ref{app:lean-statements} describe the Lean formalization,
including a guide to its declarations and proof steps.
Appendix~\ref{app:explicit-inverses} constructs the two inverses
used in the first maximality proof, and
Appendix~\ref{app:cut-errata} corrects two typographical errors
in the cut-elimination argument used in Do\v{s}en and Petri\'c's
proof of Boolean Coherence \cite{DP}.
References to \cite{DP} use the printed pagination of its
September 2007 revised version. Lean declaration names in footnotes
omit the namespace prefix \texttt{DosenPetric.}
```

### Appendix C

```latex
\section{Corrections to the cut-elimination argument used in Boolean Coherence}
\label{app:cut-errata}

Do\v{s}en and Petri\'c's proof of Boolean Coherence
\cite[\S14.2]{DP} uses the cut-elimination theorem for distributive
lattice categories proved in \cite[\S11.2]{DP}.
Our maximality proof uses Boolean Coherence as
Theorem~\ref{thm:coherence}.
We correct two typographical errors in the rank comparisons of
that cut-elimination argument. The displayed cut reductions are unchanged.

Write $L,R$ for the left and right ranks of a cut and $r=L+R$
for its total rank. Each one-sided rank counts the nodes of the
corresponding cut-formula cluster, so $L,R\geq1$.
The induction orders $(d,r)$ lexicographically, where $d$ is the
degree of the cut formula \cite[pp.~249,253]{DP}.
In the following cases, the cut formula is unchanged.

\paragraph{Page 260, case $(w\,\gamma\,3)$.}
The inequality $r<r'$ following the displayed reduction, where $r'$
is the rank of a recursive cut, should read $r'<r$.
The two recursive cuts retain the left premise $h$.
Their right cut-formula clusters lie properly inside the original
right cluster. If their ranks are $R_f,R_g$, then
$R_f<R$ and $R_g<R$. Thus both recursive cuts have smaller total
rank: $L+R_f<r$ and $L+R_g<r$.

\paragraph{Page 262, case $(w\,\vee\,1)$.}
The phrase ``whose rank is~1'' should read ``whose right rank
is~1'', as in the analogous case on p.~261.
After eliminating the first recursive cut, the selected disjunction
in the new right premise is introduced by $\vee L$, so its
cluster has one node. The left premise is still $h$.
The new cut therefore has total rank $L+1$, not~1.
The original right cluster passes through the contraction and has
$R>1$. Hence $2\leq L+1<L+R=r$, which justifies the second
application of the induction hypothesis.
```
