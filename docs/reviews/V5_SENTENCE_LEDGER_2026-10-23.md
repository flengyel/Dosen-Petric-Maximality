# V5 sentence audit ledger

Final source SHA-256: `66e7e3c24dcf986d7f424421903a79a41156282b56c7d6f0b36c1fe8b4b044ea`.

303 review units cover every prose sentence, together with displayed claims, headings, metadata and bibliography records. Units are not all grammatical sentences. The baseline had 301 units; the source-attribution sentence was replaced by three sentences. Entries retain baseline finding IDs for comparison.

## F001 — source lines 16–16

```tex
\title{Maximality of the Do\v{s}en--Petri\'c Boolean Category}
```

Title matches the precise category defined in §2 and main theorem; no claim about all alternative notions of Boolean category.

## F002 — source lines 17–17

```tex
\author{Florian Lengyel\thanks{Email: \href{mailto:flengyel@gradcenter.cuny.edu}{\texttt{flengyel@gradcenter.cuny.edu}}}}
```

Author name and supplied contact metadata retained; mailbox ownership not independently authenticated.

## F003 — source lines 18–18

```tex
\date{October 23, 2026}
```

Draft date equals the documented revision date; not a historical publication claim.

## F004 — source lines 23–26

```tex
The freely generated zero-identity Boolean category of Do\v{s}en and
Petri\'c is maximal: every additional equation between distinct parallel
arrows, closed under the proof operations and uniform formula
substitution, makes the quotient a preorder.
```

Main theorem 2.1 and §5 proof: coherence isolates a differing signed-literal edge; substitution gives K_A; Lemma 5.2 collapses all parallel pairs.

## F005 — source lines 26–28

```tex
This disproves the
nonmaximality conjecture in Section~14.2 of the September 2007 revision
of \emph{Proof-Theoretical Coherence}.
```

DP September2007 printed p322 explicitly leaves maximality of B open and conjectures nonmaximality; main theorem concerns that source category.

## F006 — source lines 28–29

```tex
Boolean Coherence reduces a new
equation to a contextual equation involving one literal.
```

Lemma4.1 uses Boolean Coherence plus explicitly constructed selectors/coselectors. This is a summary of that proof, not attribution of the selectors to the coherence theorem alone.

## F007 — source lines 29–30

```tex
Uniform
substitution extends that equation to every formula.
```

Proposition4.2 gives substitution p↦A or p↦¬A followed by the double-negation isomorphism.

## F008 — source lines 30–32

```tex
A symmetric arrow
constructed from the distributor then forces the two product
projections to coincide.
```

Lemma5.1 constructs h_A from d and proves h_A τ_A=h_A; Lemma5.2 then proves π1=π2.

## F009 — source lines 32–33

```tex
Tagged occurrence sets give explicit
coordinates for the reduction and substitution.
```

§3 defines position tags and substitution blocks; AppendixA supplies maps and coordinate formulas.

## F010 — source lines 37–38

```tex
\noindent\textit{Mathematics Subject Classification (2020).}
Primary 03G30; Secondary 03F07, 18A32.
```

MSC2020: categorical logic, structure of proofs, and categorical congruence/quotient structures are relevant to the manuscript. Codes checked in official AMS MSC2020 PDF.

## F011 — source lines 41–42

```tex
\noindent\textit{Keywords.} Boolean categories, maximality, categorial proof theory,
coherence, substitution congruences.
```

Each keyword refers to an explicitly used object, question, or condition in §§2–5.

## F012 — source lines 44–44

```tex
\section{Introduction}
```

Heading introduces question, roadmap and prior work.

## F013 — source lines 46–47

```tex
Do\v{s}en and Petri\'c's Boolean proof category admits distinct arrows
with the same source and target.
```

For p∈P, the two projections p∧p→p have distinct tagged relations; P is fixed nonempty in §2.

## F014 — source lines 47–49

```tex
Their Boolean Coherence theorem
distinguishes these arrows by relations between occurrences of
propositional variables.
```

DP printed p321 Boolean Coherence states G:B→Rel faithful; its objects count variable occurrences.

## F015 — source lines 49–50

```tex
In \cite[\S14.2, p.~322]{DP}, they leave open
whether the category is maximal and conjecture that it is not.
```

DP printed p322, last paragraph before §14.3, explicitly states both the open question and nonmaximality conjecture.

## F016 — source lines 50–52

```tex
We prove
maximality: adjoining any new arrow equation as a substitution-closed
schema identifies every pair of parallel arrows.
```

Theorem2.1 quantified over substitution congruences; §5 gives its proof.

## F017 — source lines 54–54

```tex
The proof has two parts.
```

The following roadmap divides isolation/substitution from contextual collapse, matching §§4–5.

## F018 — source lines 54–56

```tex
First, a relation distinguishing two arrows
contains an edge that can be isolated by composition with a selector
and a coselector.
```

Unequal finite relations supply an ordered pair in their symmetric difference; Lemma4.1 constructs typed i,r with singleton relations.

## F019 — source lines 56–58

```tex
This yields the contextual equation used in
Do\v{s}en and Petri\'c's relative-maximality argument
\cite[\S9.7, pp.~215--216]{DP}.
```

DP §9.7 printed pp215–216 derives the projection/injection contextual equation from differing occurrence edges. Manuscript K_A is identified with it in §4.

## F020 — source lines 58–60

```tex
Second, the distributor and zero
identities turn that contextual equation into equality of the product
projections.
```

Lemma5.2 uses h_A, zero absorption and the first-injection law to derive equality of projections.

## F021 — source lines 60–60

```tex
This second step proves the required collapse.
```

Equal projections imply any f,g:X→A coincide after pairing, as explicitly calculated in Lemma5.2.

## F022 — source lines 62–63

```tex
Do\v{s}en and Petri\'c prove maximality for cartesian categories
\cite[\S5]{DPCartesian}.
```

Supplied full Cartesian paper §5 states the maximality theorem for every Cartesian model of a new equation.

## F023 — source lines 63–65

```tex
Their proof uses coherence, uniform
substitution, and precomposition and postcomposition to reduce a new
cartesian equation to equality of the product projections.
```

Cartesian paper §5 proof chooses differing graph coordinates, substitutes all variables by p, and composes with h:p×p→A′ and j:B′→p to obtain projections.

## F024 — source lines 65–67

```tex
The
corresponding reduction for Boolean arrow equations is proved in
Sections~\ref{sec:isolation} and~\ref{sec:collapse}.
```

Internal reference: Lemma4.1, Proposition4.2 and Lemma5.2 perform the Boolean reduction. No assertion that the Cartesian paper already proves it.

## F025 — source lines 69–72

```tex
Earlier results establish maximality for lattice categories and relative
maximality for dicartesian categories
\cite[\S\S8--10]{DPBicartesian}; these results concern products and
coproducts without distribution.
```

Full DPBicartesian §§8–10: §9 proves lattice maximality; §10 gives relative dicartesian maximality without distributive d arrows.

## F026 — source lines 72–73

```tex
Related occurrence-selection
constructions appear in \cite[Lemma~6]{DPIsomorphic}.
```

DPIsomorphic full PDF Lemma6 constructs a morphism selecting specified variable occurrences, with witnessed-zero fillers. Modest related-construction claim supported.

## F027 — source lines 73–75

```tex
A differing-edge
argument also proves maximality for presentations of split preorders,
split equivalence relations, and binary relations \cite[\S16]{DPSplit}.
```

DPSplit full PDF §16 proves maximality for PF,EF,RB via their graph categories; proof starts with a pair present in Gv but absent from Gw.

## F028 — source lines 77–79

```tex
Lamarche and Stra{\ss}burger give a proof-net construction of free
categories for their Boolean-category axioms
\cite[Theorem~3.5.4]{LSFree}.
```

Supplied full LS paper Thm3.5.4: Net♭/Net♯ are free graphical and Δ–∇-strong K♭/K♯-autonomous categories. Qualifier their axioms correctly avoids identification with DP B.

## F029 — source lines 80–81

```tex
Stra{\ss}burger studies axioms for $*$-autonomous categories with
monoid and comonoid structures \cite{Strassburger}.
```

Full arXiv cs/0512086v3 §§3,5: *-autonomous base; Definition5.1 equips objects with monoid and comonoid structures. TAC publication record confirms metadata.

## F030 — source lines 82–84

```tex
F\"uhrmann and Pym interpret cut reduction by an order on arrows and
prove soundness and completeness for their net theories
\cite[Theorems~6.4--6.5]{FP}.
```

Supplied full FP paper Thms6.4–6.5 give ordered soundness/completeness for net theories; inequalities interpret cut reduction. No claim of products on the whole category.

## F031 — source lines 85–87

```tex
After precomposition with the inverse right unit isomorphism, their
negation triangle \cite[(11), p.~28]{FP} equates an endomorphism with
the identity.
```

FP printed p28 diagram(11), viewed in supplied PDF: A⊗1→A⊗(A*⊕A)→(A⊗A*)⊕A→0⊕A→A equals the right unitor; precomposition with its inverse gives id_A.

## F032 — source lines 87–88

```tex
The corresponding structural composite defines the
zero identity in \eqref{eq:zero-identity}.
```

Under ⊗↔∧,⊕↔∨,1↔top,0↔bot and corresponding η,ε, the typed path equals the DP(0ηε) composite. Structural comparison does not identify the ambient categories.

## F033 — source lines 90–92

```tex
We use the occurrence coordinates of \cite[\S9]{Notation}: occurrences
in a compound formula form tagged disjoint unions, and substitution
replaces each occurrence by its own block of occurrences.
```

§3 and AppendixA explicitly implement tagged occurrence blocks; Notes §9 source comparison assigned to appendix reviewer. No untagged collapse is claimed.

## F034 — source lines 93–95

```tex
Section~\ref{sec:occurrences} describes these blocks, and
Appendix~\ref{app:substitution} gives the commutative diagrams relating
them to Do\v{s}en and Petri\'c's ordinal substitution operation.
```

Internal references: §3 gives D_Aσ, AppendixA gives profile/block/ordinal maps and squares.

## F035 — source lines 96–97

```tex
References to \cite{DP} use the printed pagination of its September
2007 revised version.
```

All DP anchors checked here use printed pages (PDF offset+12), September2007 revision cover.

## F036 — source lines 99–99

```tex
\section{The Boolean proof category}\label{sec:category}
```

Heading matches definitions and theorem statement.

## F037 — source lines 101–101

```tex
Fix a nonempty set $P$ of propositional variables.
```

Declared standing hypothesis; used to ensure nonthinness and semantic corollary, also explicit in Theorem2.1.

## F038 — source lines 101–103

```tex
Write $\FormulaSet(P)$
for the formulas built from $P$, the constants $\top,\bot$, the binary
connectives $\wedge,\vee$, and negation $\neg$.
```

Defines exactly the source formula grammar of DP §14.1–14.2.

## F039 — source lines 103–105

```tex
Let $\B(P)$ be the
freely generated zero-identity Boolean category defined in
\cite[\S\S14.2--14.3]{DP}.
```

DP printed pp316–318 define syntactic B; p322 names B the generated zero-identity Boolean category.

## F040 — source lines 105–106

```tex
Its objects are these formulas, and its
arrows are the arrow terms of that presentation modulo its equations.
```

DP p317 states B=C(B)/E(B); formulas are source objects.

## F041 — source lines 107–107

```tex
We write $\B$ when $P$ is fixed.
```

Local abbreviation with explicit fixed-P scope.

## F042 — source lines 107–108

```tex
We recall the structure and equations
used in the proof.
```

Scope statement: §2 recalls only laws used, not a purported full presentation.

## F043 — source lines 110–111

```tex
The connectives $\wedge$ and $\vee$ give binary products and coproducts;
$\top$ is terminal and $\bot$ is initial.
```

DP B extends distributive dicartesian structure, hence finite products/coproducts with top/bot units.

## F044 — source lines 111–118

```tex
For $A_1=A$ and $A_2=B$,
denote the projections and injections by
\[
 \pi_i^{A,B}:A\wedge B\longrightarrow A_i,
 \qquad
 \iota_i^{A,B}:A_i\longrightarrow A\vee B
 \qquad(i=1,2).
\]
```

Typed projection/injection schemas: π_i:A∧B→A_i and ι_i:A_i→A∨B. Both i=1,2 and A_i declared.

## F045 — source lines 119–120

```tex
Pairing and copairing are denoted
by $\langle f,g\rangle$ and $[f,g]$, respectively.
```

Conventional pairing/copairing notation in the declared bicartesian category. No equality claim depends on undeclared operand types here.

## F046 — source lines 120–122

```tex
Write
$!_A:A\to\top$ and $\kappa_A:\bot\to A$ for the terminal and initial
arrows, and $1_A$ for the identity of $A$.
```

Terminal/initial arrows are explicitly typed; identity object given.

## F047 — source lines 122–123

```tex
Composition $g\circ f$
applies $f$ first.
```

Explicit right-to-left composition convention used consistently in displayed formulas.

## F048 — source lines 123–124

```tex
The symbols $f\wedge g$ and $f\vee g$ denote the
arrows induced by the product and coproduct bifunctors.
```

Binary product/coproduct functors C×C→C induce f∧g and f∨g; conventional categorical notation.

## F049 — source lines 126–129

```tex
The distributor is an arrow
\[
 d_{A,B,C}:A\wedge(B\vee C)\longrightarrow(A\wedge B)\vee C.
\]
```

DP §11.1 d has exactly A∧(B∨C)→(A∧B)∨C; not incorrectly declared invertible.

## F050 — source lines 130–135

```tex
Its first-injection equation is
\begin{equation}
 d_{A,B,C}\circ(1_A\wedge\iota_1^{B,C})
   =\iota_1^{A\wedge B,C}.
 \label{eq:first-injection}
\end{equation}
```

Both sides have type A∧B→(A∧B)∨C; equation is source(d∨k) after renaming variables.

## F051 — source lines 136–137

```tex
This is the coproduct-injection equation of
\cite[\S11.1, p.~234]{DP}.
```

DP printed p234 lists(d∨k), equivalent by renaming A,C to equation(1).

## F052 — source lines 139–141

```tex
Negation is represented by a functor
$\neg:\B^{\mathrm{op}}\to\B$, with specified natural
double-negation and De Morgan isomorphisms.
```

DP §14.3 p322 defines contravariant negation plus natural n-r,ρ isomorphisms; C→C^op and C^op→C are equivalent variance descriptions.

## F053 — source lines 141–142

```tex
In particular, write
$n_A:\neg\neg A\to A$ for the double-negation isomorphism.
```

DP p310 n_A^→:¬¬A→A; no cancellation of a noninvertible arrow.

## F054 — source lines 143–145

```tex
The presentation also has arrows
$\eta_A:\top\to\neg A\vee A$ and
$\epsilon_A:A\wedge\neg A\to\bot$.
```

DP §14.2 p316 has these arrows for all formulas; reduced atomic presentation is separate.

## F055 — source lines 146–151

```tex
The \emph{zero identity} is the endomorphism $0_A:A\to A$ defined by
\begin{equation}
 0_A=[\kappa_A,1_A]\circ(\epsilon_A\vee1_A)\circ d_{A,\neg A,A}
     \circ(1_A\wedge\eta_A)\circ\langle1_A,!_A\rangle.
 \label{eq:zero-identity}
\end{equation}
```

DP p317(0ηε): A→A∧top→A∧(¬A∨A)→(A∧¬A)∨A→bot∨A→A; the pairing/copairing arrows are unit isomorphisms.

## F056 — source lines 152–157

```tex
The defining zero-identity equation asserts that
\begin{equation}
 f\circ0_A=0_C\circ g
 \qquad(f,g:A\to C).
 \label{eq:zero-law}
\end{equation}
```

Zero-identity law stated explicitly in DP §14.3 p322. Two arbitrary parallel arrows f,g have type A→C and both composites A→C.

## F057a — source lines 158–159

```tex
Equation~\eqref{eq:zero-identity} is $(0\eta\epsilon)$ of
\cite[\S14.2, p.~317]{DP}.
```

Printed p.317 displays (0ηε), with the same five constituent arrows as equation (2), after identifying the notation for the two unit maps.

Disposition: corrected and rechecked.

## F057b — source lines 159–160

```tex
Its product and coproduct unit isomorphisms
are expressed here in pairing and copairing notation.
```

The source already displays both unit maps. The revised sentence states only that this manuscript expresses them by pairing and copairing; it implies no omission in the source.

Disposition: corrected and rechecked.

## F057c — source lines 161–162

```tex
Equation~\eqref{eq:zero-law} is the zero-identity law $(0I)$;
see \cite[\S14.3, p.~322]{DP}.
```

Printed p.322, §14.3, explicitly states (0I) for independent parallel arrows f,g:a→b. This matches equation (3).

Disposition: corrected and rechecked.

## F058 — source lines 164–167

```tex
\noindent\textit{Remark.}
Appendix~\ref{app:structural-diagrams} gives diagrammatic forms of
equations~\eqref{eq:first-injection}--\eqref{eq:zero-law}, with the
source and target of every arrow displayed.
```

AppendixB diagrams show every node and arrow in(1)–(3), with further constituent typing in prose.

## F059 — source lines 169–170

```tex
Whenever $\B(A,C)$ is nonempty, define $0_{A,C}=f\circ0_A$ for any
$f:A\to C$.
```

Definition requires an existing f:A→C, so it does not populate empty hom-sets; matches DP p317.

## F060 — source lines 170–171

```tex
Equation~\eqref{eq:zero-law} makes this independent of
$f$: both $f\circ0_A$ and $g\circ0_A$ equal $0_C\circ g$.
```

Apply(0I) to(f,g) and(g,g) to equate both f0_A and g0_A with 0_Cg.

## F061 — source lines 172–172

```tex
Taking $f=g$ gives $f\circ0_A=0_C\circ f$.
```

Direct specialization of(0I); domain/codomain match.

## F062 — source lines 172–175

```tex
Consequently zero arrows
absorb composition whenever the composites are defined:
$h\circ0_{A,C}=0_{A,D}$ for $h:C\to D$, and
$0_{A,C}\circ k=0_{X,C}$ for $k:X\to A$.
```

Postcomposition hf0_A defines 0_A,D witnessed by hf; precomposition f0_A k=fk0_X by naturality defines 0_X,C witnessed by fk. No missing arrows.

## F063 — source lines 177–178

```tex
Two arrows are \emph{parallel} when they have the same source and
target.
```

Definition of parallel arrows.

## F064 — source lines 178–181

```tex
A \emph{proof congruence} on $\B$ is an equivalence relation
on each hom-set preserved by composition and every arrow operation
of the presentation, including the derived operations of pairing,
copairing, and negation.
```

Pairing, copairing and contravariant arrow negation are identified as derived operations. The source primitive operations remain composition and the two tensors; the congruence condition is unchanged.

Disposition: corrected and rechecked.

## F065 — source lines 182–183

```tex
A \emph{substitution congruence} is a proof congruence also preserved
by every uniform substitution $\sigma:P\to\FormulaSet(P)$.
```

Explicit uniform endosubstitution σ:P→Form(P); congruence extended on whole arrows. No kernel of one interpretation is assumed substitution-stable.

## F066 — source lines 184–185

```tex
Here substitution acts on the entire arrow term, including its source
and target; this is rule~$(su)$ of \cite[\S2.7, p.~51]{DP}.
```

DP §2.7 p51(su) replaces p in both arrow term and type; manuscript simultaneous uniform substitution is the finite-support generalization. The direction used in the proof is single-variable substitution exactly covered by(su).

## F067 — source lines 187–187

```tex
The \emph{total congruence} identifies every parallel pair.
```

Definition: equality within every nonempty hom-set becomes universal.

## F068 — source lines 187–189

```tex
A category
is \emph{thin}, or a \emph{preorder}, when each hom-set has at most one
element.
```

Thin category definition; an empty hom-set is permitted.

## F069 — source lines 189–190

```tex
We call $\B$ \emph{maximal} when its only substitution
congruences are equality and the total congruence.
```

Explicit manuscript definition of maximality; agrees with source substitution-closed equational extension notion.

## F070 — source lines 190–191

```tex
The main result is
the following theorem.
```

Forward introductory sentence refers to Theorem2.1.

## F071 — source lines 194–194

```tex
Let $P$ be a nonempty set of propositional variables.
```

Theorem repeats nonempty P hypothesis, hence self-contained.

## F072 — source lines 194–196

```tex
The freely
generated zero-identity Boolean category $\B(P)$ of Do\v{s}en and
Petri\'c is maximal.
```

Theorem2.1 proved in §5 by isolation→K_A for all A→total congruence. Published coherence is an explicitly named input.

## F073 — source lines 196–198

```tex
Equivalently, every substitution congruence on
$\B(P)$ that identifies two distinct parallel arrows identifies all
parallel arrows.
```

Equivalent restatement follows from declared notion: a nonequality congruence contains a pair of distinct parallel arrows.

## F074 — source lines 201–201

```tex
The proof is completed in Section~\ref{sec:collapse}.
```

Internal reference resolves to §5, which contains the explicit proof of Theorem2.1.

## O01 — source lines 203–203

```tex
\section{Occurrences and substitution}\label{sec:occurrences}
```

Heading matches both occurrence constructions and substitution functors developed below.

## O02 — source lines 205–206

```tex
For a formula $A$, write $\Occ(A)$ for the finite set of positions
occupied by propositional variables in $A$.
```

Finite inductive formulas have finitely many leaf occurrences; constants contribute none. Positions are not identified by their labels.

## O03 — source lines 207–208

```tex
Appendix~\ref{app:profiles} describes substitution on these occurrence
sets by commutative diagrams.
```

Appendix A.1 explicitly constructs D, gamma, chi and the occurrence-label square, matching this forward reference.

## O04 — source lines 208–209

```tex
Repeated occurrences of the same variable
occupy distinct positions.
```

The recursive disjoint-union tags distinguish p in the two factors of p∧p, and nested paths distinguish every repeated leaf.

## O05 — source lines 209–209

```tex
We use tagged coordinates for these positions.
```

Implemented by the binary tagged sum directly below and the indexed pairs in equation (4).

## O06 — source lines 211–213

```tex
For finite sets $X,Y$, let
$X\sqcup Y=(\{1\}\times X)\cup(\{2\}\times Y)$ be their tagged
disjoint union.
```

Tags 1 and 2 are distinct; the displayed union realizes the set coproduct even when X and Y overlap or one is empty.

## O07 — source lines 213–222

```tex
disjoint union. The occurrence sets are defined recursively by
\[
 \begin{aligned}
 \Occ(p)&=\{*\},&
 \Occ(\top)&=\Occ(\bot)=\varnothing,\\
 \Occ(\neg A)&=\Occ(A),&
 \Occ(A\mathbin\star C)&=\Occ(A)\sqcup\Occ(C)
       \quad(\star\in\{\wedge,\vee\}).
 \end{aligned}
\]
```

The recursive equations define the variable singleton, empty truth-constant occurrence sets, negation-transparent occurrences, and binary tagged sums. The same operations underlie all later coordinates. No occurrence is lost by negation.

## O08 — source lines 223–224

```tex
The label map $\lambda_A:\Occ(A)\to P$ assigns to each occurrence
its underlying variable.
```

Well defined recursively: p-leaf maps to p, binary branches recurse, negation recurses, and constant maps have empty domain.

## O09 — source lines 224–224

```tex
Distinct positions may have the same label.
```

For A=p∧p, (1,*) and (2,*) are distinct and both map to p.

## O10 — source lines 225–228

```tex
The left-to-right
order gives a bijection from $\Occ(A)$ to
$\{1,\ldots,|\Occ(A)|\}$, interpreted as the empty set when the
cardinality is zero.
```

Recursively concatenate the left and right finite occurrence orders; negation leaves the order unchanged. Position rank gives the stated bijection, including the unique empty bijection.

## O11 — source lines 228–231

```tex
This bijection relates the tagged coordinates to
the finite ordinals used in \cite{DP}; Appendix~\ref{app:ordinals}
expresses the corresponding change of substitution coordinates by a
commutative square and a worked example.
```

DP §2.5 pp45–46 uses finite ordinals; Appendix A.2 gives theta_D, theta_C and delta, then a numerical example. The manuscript does not assert that ordinal coordinates retain the tags intrinsically.

## O12 — source lines 233–233

```tex
Let $\Rel$ be the category of finite sets and binary relations.
```

Definition: objects finite sets; Hom(X,Y)=P(X×Y); equality is set equality; relational composition has finite-set endpoints. Infinite P later does not become an object of this category.

## O13 — source lines 234–235

```tex
A relation $R:X\to Y$ is a subset of $X\times Y$; identities are
diagonal relations, and composition is relational composition.
```

Typed relational composite S∘R={(x,z):∃y,(x,y)∈R and (y,z)∈S}; associativity follows reassociation of existential conjunction and diagonals are identities. This supplies a covariant category, with no symmetry requirement.

## O14 — source lines 236–238

```tex
Transporting the occurrence interpretation of \cite{DP} to the
tagged coordinates gives a functor
$G:\B\to\Rel$ with $GA=\Occ(A)$.
```

For occurrence-order bijection e_A:Occ(A)→|A| and source functor G0, define Gf=e_B^{-1}∘G0(f)∘e_A for f:A→B. The e_B e_B^{-1} middle terms cancel in composition; G1_A is diagonal. DP §2.9 pp59–60 and §14.2 pp317,321 supply G0. This transports a covariant functor, not the contravariant negation functor.

## O15 — source lines 239–243

```tex
For example,
\[
 G\pi_1^{A,C}=\{((1,x),x):x\in\Occ(A)\},\qquad
 G\iota_1^{A,C}=\{(x,(1,x)):x\in\Occ(A)\}.
\]
```

Gπ1 is the graph of restriction to the first tagged summand; Gι1 is the first-tag insertion graph. Both have the required source and target occurrence sets. DP p60 gives these relations in ordinal coordinates.

## O16 — source lines 244–244

```tex
The second projection and injection use tag~$2$.
```

Dual formulas replace (1,x) with (2,x), where x is an occurrence of the second factor. This matches the ordinal offset n on DP p60.

## O17 — source lines 244–246

```tex
Pairing takes the
union of the two relations after tagging their targets; copairing
takes the union after tagging their sources.
```

For f:X→A,g:X→B, pairing gives {(x,(1,a)):(x,a)∈Gf}∪{(x,(2,b)):(x,b)∈Gg}; for f:A→X,g:B→X the analogous tags are on the domain. These formulas follow from diagonal/codiagonal and tensor relations, DP p60.

## O18 — source lines 246–254

```tex
takes the union after tagging their sources. The relation $Gd_{A,B,C}$
is the graph of the rebracketing bijection
\[
 \Occ(A)\sqcup\bigl(\Occ(B)\sqcup\Occ(C)\bigr)
 \longrightarrow
 \bigl(\Occ(A)\sqcup\Occ(B)\bigr)\sqcup\Occ(C),
\]
which preserves each occurrence of $A,B,C$
\cite[\S2.9, p.~60]{DP}. Zero arrows have empty relations.
```

Gd sends (1,a)↦(1,(1,a)), (2,(1,b))↦(1,(2,b)), and (2,(2,c))↦(2,c). These cases exhaust the source and invert uniquely. DP p60 assigns the identity ordinal relation to d; flattening the tags gives exactly this bijection. The next sentence about zeros is separately assessed.

## O19 — source lines 254–254

```tex
Zero arrows have empty relations.
```

The primitive zero endomorphism has empty relation in §12.5; witnessed zero f∘0_A therefore has empty relation by composition. DP §14.2 p317 explicitly treats eta and epsilon as zero arrows with empty G. This does not infer equality from an empty relation and does not populate absent hom-sets.

## O20 — source lines 256–260

```tex
\begin{theorem}[Boolean Coherence, Do\v{s}en--Petri\'c]
\label{thm:coherence}
The functor $G:\B\to\Rel$ is faithful: parallel arrows $f,g$ of
$\B$ are equal if and only if $Gf=Gg$.
\end{theorem}
```

Boolean Coherence on DP printed p321 states G:B→Rel faithful. Equality implies equal images by functorial well-definedness; the converse is faithfulness. Transport by e_A preserves this theorem. All arrows are parallel as explicitly required.

## O21 — source lines 262–262

```tex
This is \cite[\S14.2, p.~321]{DP}.
```

The exact named theorem Boolean Coherence and conclusion occur at the bottom of printed p321 (PDF p333).

## O22 — source lines 262–264

```tex
In particular, for $p\in P$, the
two projections $p\wedge p\to p$ have different occurrence
relations, so $\B$ is nonthin.
```

Gπ1={((1,*),*)}, Gπ2={((2,*),*)}; the distinct tagged domain points make the relations unequal. A functor maps equal arrows to equal relations, so the projections differ. Nonempty P, fixed in §2, supplies p. No faithfulness is actually needed for this implication.

## O23 — source lines 264–265

```tex
Below, coherence is applied to
equations in $\B$; these equations then pass to its quotients.
```

Checked §§4–5: isolation, symmetric h, final second-block equality and terminal-injection last equality use coherence in B. Quotient equalities follow congruence. No reflection of quotient equality by G or cancellation of j_A is invoked.

## O24 — source lines 267–267

```tex
A \emph{signed literal} is $p$ or $\neg p$ for $p\in P$.
```

Definition distinguishes the two polarities, including the same underlying p.

## O25 — source lines 268–269

```tex
A formula is in \emph{negation normal form} when negation occurs only
immediately before a propositional variable.
```

This excludes negated constants, binary formulas and double negation, while allowing all positive binary/constant constructions over signed literals.

## O26 — source lines 269–272

```tex
The double-negation and
De Morgan isomorphisms, including the isomorphisms for the truth
constants, give an isomorphism $a_A:A\to A^\circ$ to a formula in
negation normal form.
```

DP §14.1 printed pp313–314 constructs i_A:A→FA and its inverse recursively, with explicit truth-constant clauses. The manuscript a_A has the same orientation. These structural comparisons remain arrows in B.

## O27 — source lines 272–273

```tex
Its occurrence relation is the graph of the
correspondence of positions \cite[\S14.1, pp.~313--315]{DP}.
```

DP p314 assigns identity ordinal relations to n,r,rho; the recursive tensor/composition construction preserves the left-to-right occurrence enumeration. Transport yields the bijection between tagged source and normalized target positions.

## O28 — source lines 275–276

```tex
For arrows between formulas in negation normal form, every edge of
the occurrence relation joins occurrences of the same signed literal.
```

Normalize the full term through C^neg≅B and C^neg≃C (DP pp318,321). At normal endpoints the comparisons are identities; each positive primitive preserves the signed object-generators, and eta_p/epsilon_p/zero contribute no edges. Relational composition and the tensors preserve agreement. No faithfulness is needed for this invariant.

## O29 — source lines 277–278

```tex
Indeed, the equivalent presentation of \cite[\S14.2, pp.~318--321]{DP}
has signed literals as generators.
```

DP p318 defines C on positive formulas generated by P∪P^neg, with only atomic eta_p/epsilon_p. It states C^neg≅B and p321 proves C^neg≃C. Thus C is equivalent to B, not literally isomorphic via the normalization on objects; wording equivalent is correct.

## O30 — source lines 278–280

```tex
Its positive structural generators
preserve these labels; zero endomorphisms and the arrows $\eta_p$ and
$\epsilon_p$ have empty relations.
```

The source reduced grammar includes positive structural families, zero endomorphisms and atomic eta/epsilon. The structural relations preserve signed labels, and the specified remaining relations are empty.

Disposition: corrected and rechecked.

## O31 — source lines 280–281

```tex
Composition and both tensor
operations preserve label agreement.
```

Composition preserves signed-label agreement through the common intermediate occurrence. Each tensor tags the two component relations without changing literal labels. These are the source reduced primitive operations.

Disposition: corrected and rechecked.

## O32 — source lines 281–282

```tex
The equivalence with $\B$ preserves the occurrence
interpretation.
```

DP p321 chooses F beta_p=beta_p and its inclusion counterpart, while pp313–314 send comparison arrows to identities under G. Hence the diagram of occurrence functors commutes, with tagged coordinate changes on arbitrary objects. At normal objects it yields exactly the invariant used here.

## O33 — source lines 284–285

```tex
Substitution replaces each occurrence of a variable by a separate
block of occurrences of its substituted formula.
```

Structural substitution recursively inserts a fresh syntactic copy at each leaf. This is a statement about endpoint occurrence sets, not an edgewise expansion law for arbitrary arrow relations.

## O34 — source lines 286–287

```tex
Appendix~\ref{app:profiles} describes these blocks and their label maps
by commutative diagrams, following \cite[\S9]{Notation}.
```

Read public v8 TeX §9.1–9.3: its D, tagged target C, profiles and fibre squares are the same construction. Appendix A.1 makes the occurrence-to-block bijection and label square explicit.

## O35 — source lines 288–289

```tex
Let $Q$ be a set of propositional variables and
$\sigma:P\to\FormulaSet(Q)$ a substitution.
```

Typed data for a formula substitution. Q may be empty; closed formulas such as top remain available. P need not be finite.

## O36 — source lines 289–296

```tex
$\sigma:P\to\FormulaSet(Q)$ a substitution. If $A[\sigma]$ denotes the
result of uniform substitution, there is a canonical bijection
\begin{equation}
 \Occ(A[\sigma])\cong D_{A,\sigma},\qquad
 D_{A,\sigma}=\coprod_{x\in\Occ(A)}
                  \Occ\bigl(\sigma(\lambda_A(x))\bigr).
 \label{eq:occ-substitution}
\end{equation}
```

The bijection is recursively determined: variable p uses its unique old leaf and the new occurrence; constants give empty maps; binary connectives prepend the branch tag to the old coordinate; negation changes neither occurrence set. Its inverse forgets the paired decomposition by the same recursion. Thus canonical is justified here by specified recursive syntax, not by an unsupported uniqueness among arbitrary bijections.

## O37 — source lines 297–298

```tex
The set on the right consists of pairs $(x,t)$, where $x$ is an old
occurrence and $t$ is an occurrence within the formula inserted there.
```

This is exactly the dependent disjoint-union definition in equation (4); membership of t depends on lambda_A(x).

## O38 — source lines 299–301

```tex
Induction on $A$ proves the bijection: the variable case has one
block, the constant cases have none, binary connectives form tagged
unions, and negation preserves the occurrence set.
```

All five formula-constructor kinds are covered. Under negation sigma still substitutes the same formula and Occ(neg B)=Occ(B); no polarities or negation-variable conditions are silently imposed.

## O39 — source lines 301–303

```tex
In particular,
two occurrences of the same variable give two separately tagged
copies of its substituted formula.
```

If x≠x′ and lambda_A(x)=lambda_A(x′)=p, (x,t)≠(x′,t), even though both local t lie in Occ(sigma(p)).

## O40 — source lines 305–306

```tex
The organization of these blocks is expressed by a square of sets and
functions.
```

The square belongs to Set, not Rel_fin: E_sigma and P may be infinite. This wording explicitly avoids a finite-object claim.

## O41 — source lines 306–306

```tex
Put $E_\sigma=\coprod_{p\in P}\Occ(\sigma(p))$.
```

This set exists for arbitrary P and finite fibres, with elements (p,t). It need not be finite; no assertion of finiteness is made.

## O42 — source lines 307–309

```tex
Define $\operatorname{pr}_D:D_{A,\sigma}\to\Occ(A)$ and
$\operatorname{pr}_E:E_\sigma\to P$ by
$\operatorname{pr}_D(x,t)=x$ and $\operatorname{pr}_E(p,t)=p$.
```

Both are total first-coordinate maps with their displayed domains; empty fibres simply contribute no pair.

## O43 — source lines 310–312

```tex
The function
$\widehat\lambda_{A,\sigma}:D_{A,\sigma}\to E_\sigma$ sends
$(x,t)$ to $(\lambda_A(x),t)$.
```

Membership t∈Occ(sigma(lambda_A(x))) is exactly the required target-fibre membership. No injectivity is asserted or needed.

## O44 — source lines 312–321

```tex
$(x,t)$ to $(\lambda_A(x),t)$. Thus
\begin{equation}
\begin{tikzcd}[column sep=large,row sep=large]
 D_{A,\sigma}\arrow[r,"\widehat\lambda_{A,\sigma}"]
   \arrow[d,"\operatorname{pr}_D"']
   &E_\sigma\arrow[d,"\operatorname{pr}_E"]\\
 \Occ(A)\arrow[r,"\lambda_A"']&P.
\end{tikzcd}
\label{eq:block-square}
\end{equation}
```

The square commutes because pr_E(hatlambda(x,t))=lambda_A(x)=lambda_A(pr_D(x,t)). Its arrow directions and endpoint types are all correct.

## O45 — source lines 322–323

```tex
Both routes send $(x,t)$ to the variable $\lambda_A(x)$ whose
substituted formula contains $t$.
```

Direct evaluation of both typed composites; the wording does not confuse t with its eventual variable label in Q.

## O46 — source lines 323–325

```tex
The upper arrow forgets which
occurrence of that variable supplied the copy; the source $D_{A,\sigma}$
retains it.
```

hatlambda retains only the underlying p and local t; repeated old occurrences x with equal labels map to the same (p,t). D retains x. If no repeated labels exist the map happens to be injective, but forgetting the coordinate still accurately describes its formula.

## O47 — source lines 327–331

```tex
Substitution on arrow terms induces a functor
\[
 F_\sigma:\B(P)\longrightarrow\B(Q),\qquad
 A\longmapsto A[\sigma],\quad f\longmapsto f[\sigma].
\]
```

For each f:A→B, raw substitution gives f[sigma]:A[sigma]→B[sigma]. Object and arrow maps are typed and covariant. This is distinct from substitution of occurrence relations alone.

## O48 — source lines 332–333

```tex
Rule~$(su)$ makes this functor well defined on arrow terms modulo the
defining equations.
```

DP §2.7 p51 gives substitution closure and states that equations have formula variables, with no fixed letters, and work for arbitrary P. Induction on equational derivations then preserves the full defining schemas under simultaneous substitution across P,Q. The paragraph needs that surrounding schema fact as well as the displayed one-variable rule; citation is adequate, but one could more exactly say The defining equations are preserved by substitution.

## O49 — source lines 333–334

```tex
It preserves identities, composition, and the
specified arrow operations.
```

Raw substitution commutes by definition with identity, composition, tensors and indexed primitive families; derived pairing, copairing and negation therefore commute as composites. Quotient equality preservation established in the previous sentence gives the functor laws.

## O50 — source lines 334–336

```tex
For each arrow, the blocks in
\eqref{eq:occ-substitution} describe the occurrence sets of its
substituted source and target.
```

Apply the formula-level bijection independently to the source and target. This deliberately does not claim that G(f[sigma]) is obtained by simply replacing every edge of Gf with a block identity; such a stronger assertion is not proved here.

## C001 — source lines 338–338

```tex
\section{Isolating an occurrence}\label{sec:isolation}
```

Heading matches the next lemma: isolation of one differing occurrence edge.

## C002 — source lines 340–340

```tex
Put $j_A=\iota_1^{A,\top}:A\to A\vee\top$.
```

Definition: the first coproduct injection has exactly the stated source A and target A∨top.

## C003 — source lines 340–346

```tex
The contextual equation
needed in the proof is
\begin{equation}
 j_A\circ\pi_1^{A,\bot}
   =0_{A\wedge\bot,A\vee\top}.
 \tag{$K_A$}\label{eq:context}
\end{equation}
```

K_A compares arrows A∧bot→A∨top. Its left side j_A∘π₁ is an existing-arrow witness for the zero on its right. It is a proposed additional contextual equation, not asserted to hold in B.

## C004 — source lines 347–350

```tex
The right-hand side is also
$\iota_2^{A,\top}\circ!_\bot\circ\pi_2^{A,\bot}$: its occurrence
relation is empty, so Boolean Coherence identifies it with the zero
arrow.
```

The composite is A∧bot --π₂→ bot --!bot→ top --ι₂→ A∨top. Both intermediate occurrence sets are empty, so its relation equals that of the witnessed zero; faithfulness in B is the published input.

## C005 — source lines 350–351

```tex
Thus \eqref{eq:context} is the contextual equation of
\cite[\S9.7, pp.~215--216]{DP}.
```

The source printed pp.215–216 gives first-injection∘first-projection = second-injection∘(bot→top)∘second-projection. The preceding sentence identifies the latter with this manuscript’s witnessed zero. This is an accurate translation, not an assertion the source calls it zero between every pair.

## C006 — source lines 354–366

```tex
For distinct parallel arrows $f,g:A\to C$ in $\B$, there are a
signed literal $\ell$ and arrows
\[
 i:\ell\wedge\bot\longrightarrow A,
 \qquad r:C\longrightarrow\ell\vee\top
\]
such that, after possibly interchanging $f$ and $g$,
\[
 r\circ f\circ i=j_\ell\circ\pi_1^{\ell,\bot},
 \qquad
 r\circ g\circ i=0_{\ell\wedge\bot,\ell\vee\top}.
\]
\end{lemma}
```

Hypotheses: parallel distinct arrows f,g in B. Normalize; use faithfulness to select a differing edge; same-signed-label preservation supplies ℓ; selector and coselector isolate it. Both displayed equalities are in B at ℓ∧bot→ℓ∨top. The existing right-hand composite witnesses the zero.

## C007 — source lines 369–370

```tex
First replace $f,g$ by $a_C\circ f\circ a_A^{-1}$ and
$a_C\circ g\circ a_A^{-1}$.
```

Both composites have source A° and target C° because a_A⁻¹:A°→A and a_C:C→C°. This uses previously introduced normalizing isomorphisms.

## C008 — source lines 370–371

```tex
These remain distinct, so it suffices to
construct the arrows for the negation normal forms $A^\circ,C^\circ$.
```

If the normalized arrows were equal, compose with a_C⁻¹ on the left and a_A on the right to recover f=g; this contradicts distinctness.

## C009 — source lines 372–374

```tex
If their selector and coselector are $i^\circ,r^\circ$, the required
arrows for the original formulas are
$a_A^{-1}\circ i^\circ$ and $r^\circ\circ a_C$.
```

The transported selector has type ℓ∧bot→A; the transported coselector has type C→ℓ∨top. Inserting the inverse identities recovers the normalized composites.

## C010 — source lines 375–375

```tex
We may therefore assume that $A,C$ are in negation normal form.
```

The preceding construction proves the reduction to negation-normal endpoints without strengthening the statement.

## C011 — source lines 377–377

```tex
Faithfulness of $G$ gives an edge belonging to exactly one of $Gf,Gg$.
```

Distinct parallel arrows have unequal relations by faithful G. Unequal subsets have a member of their symmetric difference; this uses classical reasoning, permitted in this ordinary mathematical argument.

## C012 — source lines 378–379

```tex
Interchange $f,g$ if necessary, and choose
$(x,y)\in Gf\setminus Gg$.
```

A symmetric-difference edge can be oriented into Gf minus Gg by exchanging the names of f and g, as allowed by the statement.

## C013 — source lines 379–380

```tex
The occurrences $x$ and $y$ have the same
signed literal $\ell$.
```

The preceding Section 3 establishes signed-label preservation for normal-form endpoints, which now applies. No faithfulness of a quotient is used.

## C014 — source lines 380–380

```tex
Set $D=\ell\wedge\bot$ and $E=\ell\vee\top$.
```

Definitions; each of D and E has exactly one variable occurrence, tagged by its literal summand/factor.

## C015 — source lines 381–387

```tex
For every formula $V$, the arrows
\[
 b_V=\kappa_V\circ\pi_2^{\ell,\bot}:D\to V,
 \qquad
 t_V=\iota_2^{\ell,\top}\circ!_V:V\to E
\]
have empty occurrence relations.
```

b_V:D→bot→V uses initiality; t_V:V→top→E uses terminality. Every type exists for arbitrary V without introducing a zero arrow into an empty hom-set. Their relations are empty because one intermediate occurrence set is empty.

## C016 — source lines 389–390

```tex
Construct the selector $i:D\to A$ recursively along the tagged path
to $x$.
```

Induction follows the finite parse-tree path of the chosen occurrence. This path cannot enter a constant; the only leaves reached are the selected signed literal.

## C017 — source lines 390–390

```tex
At the selected literal, use $\pi_1^{\ell,\bot}$.
```

Base selector is D=ℓ∧bot→ℓ; its relation selects the sole ℓ occurrence.

## C018 — source lines 391–393

```tex
At a conjunction, pair the recursively constructed arrow with $b_V$
for the unselected factor, placing it in the order specified by the
tag.
```

For chosen branch V₁∧V₂, recursively constructed D→V_i and b_{V_j}:D→V_j have common source, so pairing is typed. The zero-relation filler adds no edge; target tag identifies the chosen side.

## C019 — source lines 393–394

```tex
At a disjunction, compose the recursively constructed arrow
with the injection of the selected summand.
```

For selected summand V_i, compose D→V_i with V_i→V₁∨V₂. The injection inserts the appropriate target tag.

## C020 — source lines 394–396

```tex
The displayed rules for
$G$ show inductively that $Gi$ consists of the single edge from the
sole occurrence of $D$ to $x$.
```

Induct on path length: literal case one edge, conjunction adds empty relation on the other factor, disjunction retags the one edge. Constants are excluded by occurrence existence; repeated equal literals remain distinct by path tags.

## C021 — source lines 398–398

```tex
Construct $r:C\to E$ dually along the path to $y$.
```

Dual recursion is over the finite path of an actual occurrence of C, so its selected terminal node is ℓ, not a constant.

## C022 — source lines 399–399

```tex
At the selected literal, use $\iota_1^{\ell,\top}$.
```

Base coselector ℓ→E=ℓ∨top has one edge to its sole occurrence.

## C023 — source lines 400–401

```tex
At a conjunction, first project to the selected factor and then apply
the recursively constructed arrow.
```

Project V₁∧V₂→V_i before recursively applying V_i→E; composition has the required source and target, and keeps only the selected source tag.

## C024 — source lines 401–402

```tex
At a disjunction, copair that
arrow with $t_V$ on the unselected summand.
```

The recursive V_i→E and t_{V_j}:V_j→E share codomain E; their copair is typed and adds no edge from the unused summand.

## C025 — source lines 402–403

```tex
Thus $Gr$ is the single
edge from $y$ to the sole occurrence of $E$.
```

By the two branch cases and the literal base case, exactly y survives; tagging preserves its position even if labels repeat.

## C026 — source lines 405–407

```tex
Relational composition now makes $G(r\circ f\circ i)$ the one-edge
relation from $\Occ(D)$ to $\Occ(E)$, whereas
$G(r\circ g\circ i)$ is empty.
```

Gi selects exactly x and Gr exactly y, so the composite relation contains its unique possible pair iff (x,y) lies in the middle relation. It lies in Gf and not Gg.

## C027 — source lines 407–408

```tex
Boolean Coherence gives the asserted
equations.
```

Compare the first composite with j_ℓ∘π₁ (the one-edge relation) and the second with its witnessed zero (empty relation). All four are parallel arrows in original B, where coherence applies.

## C028 — source lines 412–414

```tex
If a substitution congruence $\theta$ on $\B$ identifies distinct
parallel arrows, then \eqref{eq:context} holds modulo $\theta$ for
every formula $A$.
```

Explicit assumption is substitution-stable congruence identifying distinct parallels. Isolation yields one K_ℓ; positive substitution or negative substitution plus n_A transports it to every formula. This does not assert arbitrary proof congruences are substitution closed.

## C029 — source lines 418–419

```tex
Lemma~\ref{lem:isolation} and compatibility with composition give
\eqref{eq:context} for a signed literal $\ell$.
```

The two isolation composites become equal modulo θ by congruence compatibility. Their original-B equalities identify the classes with the two sides of K_ℓ.

## C030 — source lines 420–420

```tex
If $\ell=p$, let $\sigma$ substitute $A$ for $p$ and fix the other variables.
```

σ:P→Form(P) is an endosubstitution even when A itself contains p; uniform substitution is simultaneous, not a recursive fixed-point replacement.

## C031 — source lines 421–424

```tex
This yields \eqref{eq:context} for $A$: under
\eqref{eq:occ-substitution}, the literal occurrence in each endpoint
becomes the block $\Occ(A)$, and the arrow operations are preserved
by $F_\sigma$.
```

F_σ sends the literal source and target to A∧bot and A∨top, preserves j,π₁ and the defining zero composite, and θ is substitution stable. The occurrence-block explanation describes endpoints, not an unjustified edgewise formula for arbitrary substituted arrows.

## C032 — source lines 424–425

```tex
Appendix~\ref{app:shared} describes this
one-occurrence case of the substitution diagrams.
```

Appendix A.3 lines775–785 explicitly treats both positive and negative one-literal cases.

## C033 — source lines 427–428

```tex
If $\ell=\neg p$, substitute $\neg A$ for $p$, obtaining the equation
for $\neg\neg A$.
```

Substituting p↦¬A into ℓ=¬p yields ¬¬A in both endpoints; η/ε and zero structure are uniformly substituted as whole terms.

## C034 — source lines 428–428

```tex
Transport it along $n_A:\neg\neg A\to A$.
```

The introduced double-negation isomorphism provides the stated forward map and an inverse; the following diagram specifies the endpoint transport.

## C035 — source lines 429–430

```tex
Explicitly, let
$k_A=j_A\circ\pi_1^{A,\bot}:A\wedge\bot\to A\vee\top$.
```

k_A has source A∧bot and target A∨top; it abbreviates the left side of K_A, not the full equation.

## C036 — source lines 431–439

```tex
The product and coproduct equations give the commutative square
\[
\begin{tikzcd}[column sep=large,row sep=large]
 A\wedge\bot\arrow[r,"k_A"]\arrow[d,"n_A^{-1}\wedge1_\bot"']
   &A\vee\top\\
 \neg\neg A\wedge\bot\arrow[r,"k_{\neg\neg A}"']
   &\neg\neg A\vee\top\arrow[u,"n_A\vee1_\top"'].
\end{tikzcd}
\]
```

Long route: A∧bot --n_A⁻¹∧1→¬¬A∧bot --k_nnA→¬¬A∨top --n_A∨1→A∨top. Product projection naturality, coproduct injection naturality and n_A∘n_A⁻¹=1 identify it with k_A. Each intermediate type matches.

## C037 — source lines 440–441

```tex
Precomposition and postcomposition of the zero arrow give a zero
arrow by absorption.
```

Transport the existing zero at ¬¬A∧bot→¬¬A∨top along the displayed arrows. Witnessed-zero absorption was proved in Section 2 and produces the witnessed zero at the new endpoints; no nonexistent arrows are supplied.

## C038 — source lines 441–442

```tex
The equation for $\neg\neg A$ therefore gives
\eqref{eq:context} for $A$.
```

Apply congruence compatibility to the two-sided transport; left side becomes k_A and right side the witnessed zero, yielding K_A modulo θ.

## C039 — source lines 445–445

```tex
\section{Contextual collapse}\label{sec:collapse}
```

Heading accurately describes the result: K_A for all A entails thin quotient.

## C040 — source lines 447–448

```tex
The distributor produces an arrow that treats two copies of $A$
symmetrically.
```

The forthcoming h_A is explicitly constructed from d and bicartesian operations; its relation folds the two tags, and coherence proves symmetry.

## C041 — source lines 448–449

```tex
This symmetry converts the contextual equation into
an equation between the projections.
```

Accurate roadmap: symmetry yields j_Aπ₁≡j_Aπ₂ first, and the later B=top computation removes the contextual injection without cancellation.

## C042 — source lines 452–459

```tex
For formulas $A,B$, define
\[
 \begin{aligned}
 u_A^B&=d_{A,B,A}\circ(1_A\wedge\iota_2^{B,A})
       :A\wedge A\longrightarrow(A\wedge B)\vee A,\\
 h_A^B&=[\pi_1^{A,B},1_A]\circ u_A^B:A\wedge A\longrightarrow A.
 \end{aligned}
\]
```

1_A∧ι₂^{B,A}:A∧A→A∧(B∨A); d_{A,B,A} gives (A∧B)∨A; [π₁^{A,B},1_A] maps that coproduct to A. Thus both displayed definitions have exactly their declared endpoints.

## C043 — source lines 460–460

```tex
The arrow $h_A^B$ is independent of $B$.
```

For B and B′, both h arrows lie in Hom(A∧A,A), and the proof gives the same tagged fold relation independent of both parameters; original-B coherence yields equality.

## C044 — source lines 460–463

```tex
Writing it as $h_A$ and
putting $\tau_A=\langle\pi_2^{A,A},\pi_1^{A,A}\rangle:
A\wedge A\to A\wedge A$, one has
$h_A\circ\tau_A=h_A$.
```

Both projections have source A∧A and target A; pairing them in reverse order therefore has type A∧A→A∧A. The fold relation is unchanged by that swap.

Disposition: corrected and rechecked.

## C045 — source lines 467–468

```tex
The relation of $u_A^B$ sends $(1,x)$ to $(1,(1,x))$ and $(2,x)$
to $(2,x)$ in $\bigl(\Occ(A)\sqcup\Occ(B)\bigr)\sqcup\Occ(A)$.
```

Tensor with injection retains first tag A and sends second A into the second disjunction branch; rebracketing d sends them to ((1,(1,x))) and (2,x). No B occurrences receive edges. Domain tags are those of Occ(A)⊔Occ(A).

## C046 — source lines 469–473

```tex
Postcomposing $u_A^B$ with
$[\pi_1^{A,B},1_A]:(A\wedge B)\vee A\to A$ gives
\[
 Gh_A^B=\{((1,x),x),((2,x),x):x\in\Occ(A)\}.
\]
```

The copairing [π₁^{A,B},1_A] has source (A∧B)∨A and target A. Its source equals the target of u_A^B, so their indicated postcomposition is typed and has the displayed fold relation.

Disposition: corrected and rechecked.

## C047 — source lines 474–475

```tex
This relation is independent of $B$ and invariant under exchange of
the two source tags.
```

The target formula A and source A∧A are independent of B. Swapping the two source tags leaves the two-element-per-x description unchanged, including the empty-occurrence case.

## C048 — source lines 475–475

```tex
Boolean Coherence proves both assertions.
```

All comparisons are in B, either h_A^B vs h_A^{B′} or h_A∘τ_A vs h_A. Faithfulness yields the required equalities; none is inferred in the quotient.

## C049 — source lines 479–480

```tex
Let $\theta$ be a proof congruence on $\B$ such that
\eqref{eq:context} holds modulo $\theta$ for every formula $A$.
```

Hypothesis requires K_A for all formulas and a proof congruence only. The proof does not invoke substitution closure, which belonged solely to the preceding proposition.

## C050 — source lines 481–481

```tex
Then $\B/\theta$ is a preorder.
```

Conclusion means every parallel hom-set in B/θ has at most one element. The proof derives equal projections for each A and then uses product pairing on arbitrary parallels.

## C051 — source lines 485–485

```tex
Write $\equiv$ for equality modulo $\theta$.
```

Notation is explicitly fixed; equalities in original B continue to be written =, while new quotient equalities use ≡.

## C052 — source lines 486–487

```tex
The quotient retains products and coproducts: their pairing,
copairing, and defining equations pass to equivalence classes.
```

Congruence under pairing/copairing makes induced operations well defined. Their β and η identities descend and imply existence and uniqueness of maps from/to the product/coproduct in the quotient. Terminality and initiality also persist because all original maps to/from the constants were already unique.

## C053 — source lines 488–498

```tex
Using $B=\bot$ in Lemma~\ref{lem:symmetric}, copairing and
\eqref{eq:context} give
\begin{equation}
 \begin{aligned}
 j_A\circ h_A
   &=[j_A\circ\pi_1^{A,\bot},j_A]\circ u_A^\bot\\
   &\equiv[0_{A\wedge\bot,A\vee\top},j_A]\circ u_A^\bot\\
   &=j_A\circ\pi_2^{A,A}.
 \end{aligned}
 \label{eq:second-block}
\end{equation}
```

All terms have source A∧A and target A∨top. First equality uses j_A postcomposition through a copair; middle uses K_A inside the first copair component; last is original-B relation equality justified immediately below. u_A^bot is still an existing arrow; no empty hom-set is enlarged.

## C054 — source lines 499–500

```tex
For the last equality, both occurrence relations discard the first
source tag and send $(2,x)$ to $(1,x)$ in $\Occ(A)\sqcup\varnothing$.
```

u_A^bot routes first A into the first source summand of the copair, which zero kills; second A enters j_A and reaches first target tag. j_A∘π₂ has exactly this relation.

## C055 — source lines 501–501

```tex
Thus it is an equation of $\B$ by Boolean Coherence.
```

The last equality compares parallel arrows of B before passage to θ; using faithfulness here is noncircular.

## C056 — source lines 502–506

```tex
Precomposing \eqref{eq:second-block} with $\tau_A$ and using
$h_A\circ\tau_A=h_A$ yields
\[
 j_A\circ\pi_1^{A,A}\equiv j_A\circ\pi_2^{A,A}.
\]
```

Precompose both sides with τ_A:A∧A→A∧A. h_Aτ_A=h_A and π₂τ_A=π₁ give j_Ah_A≡j_Aπ₁; combine with j_Ah_A≡j_Aπ₂ to obtain the displayed equivalence. No cancellation of j_A occurs.

## C057 — source lines 507–507

```tex
Now precompose with $\langle1_A,0_A\rangle:A\to A\wedge A$.
```

The pair is well typed because 1_A and 0_A share source A and codomain A; projections of it are 1_A and 0_A.

## C058 — source lines 508–514

```tex
It follows that
\begin{equation}
 j_A\equiv j_A\circ0_A
   =0_{A,A\vee\top}
   =\iota_2^{A,\top}\circ!_A.
 \label{eq:terminal-injection}
\end{equation}
```

Both sides have source A and target A∨top. Precomposition gives j_A≡j_A0_A. The first = is the witnessed-zero definition with witness j_A; the last = follows from the next sentence’s original-B coherence argument.

## C059 — source lines 515–516

```tex
The last equality holds by coherence, since the composite through
$\top$ has empty occurrence relation.
```

ι₂^{A,top}∘!_A factors through top with empty occurrence set. It and j_A0_A are parallel empty-relation arrows in B, so original-B coherence applies.

## C060 — source lines 518–519

```tex
The arrows $s=\iota_2^{A,\top}:\top\to A\vee\top$ and
$t=!_{A\vee\top}:A\vee\top\to\top$ are inverse in the quotient.
```

s:top→A∨top and t:A∨top→top are explicitly typed; inverse laws are shown in the next three sentences, one already in B and one modulo θ.

## C061 — source lines 520–520

```tex
Indeed, $t\circ s=1_\top$ by terminality.
```

t∘s:top→top equals 1_top because top is terminal. This holds before quotienting.

## C062 — source lines 520–524

```tex
Equation
\eqref{eq:terminal-injection} gives
$(s\circ t)\circ\iota_1^{A,\top}\equiv\iota_1^{A,\top}$, and
terminality gives
$(s\circ t)\circ\iota_2^{A,\top}=\iota_2^{A,\top}$.
```

On first injection, tι₁=!_A, so stι₁=s!_A≡j_A=ι₁ by the earlier equation. On second injection, ts=1_top, so sts=s=ι₂. The use of ≡ vs = is correct.

## C063 — source lines 525–525

```tex
The coproduct property therefore gives $s\circ t\equiv1_{A\vee\top}$.
```

In the quotient, st and identity have equal restrictions along both coproduct injections by preceding calculations; uniqueness in the retained coproduct universal property yields equality.

## C064 — source lines 526–527

```tex
Hence $A\vee\top$, and by coproduct symmetry also $\top\vee A$,
is terminal in the quotient.
```

A∨top is isomorphic to terminal top in the quotient, hence terminal. The structural coproduct symmetry top∨A≅A∨top is preserved by the quotient, so top∨A is also terminal.

## C065 — source lines 527–531

```tex
In particular,
\begin{equation}
 \iota_2^{\top,A}\equiv\iota_1^{\top,A}\circ!_A.
 \label{eq:other-injection}
\end{equation}
```

ι₂^{top,A} and ι₁^{top,A}∘!_A are parallel A→top∨A. Terminality in the quotient makes them equal. This is not asserted as an original-B equality.

## C066 — source lines 533–533

```tex
Evaluate the same arrow $h_A$ using $B=\top$.
```

Independence of B has already been proved as equality in B, so using the top-based expression for the same h_A is justified.

## C067 — source lines 534–546

```tex
Substituting \eqref{eq:other-injection} into its defining expression
and applying \eqref{eq:first-injection} gives
\[
 \begin{aligned}
 h_A
   &\equiv[\pi_1^{A,\top},1_A]\circ d_{A,\top,A}
       \circ(1_A\wedge\iota_1^{\top,A})
       \circ(1_A\wedge!_A)\\
   &=[\pi_1^{A,\top},1_A]\circ\iota_1^{A\wedge\top,A}
       \circ(1_A\wedge!_A)\\
   &=\pi_1^{A,A}.
 \end{aligned}
\]
```

Types along expanded route: A∧A --1∧!→A∧top --1∧ι₁→A∧(top∨A) --d→(A∧top)∨A --[π₁,1]→A. Equation(1) shortens the middle two to ι₁^{A∧top,A}; copair β gives π₁^{A,top}; product naturality then gives π₁^{A,A}. First step only modulo θ, following equalities in B.

## C068 — source lines 547–548

```tex
Since $h_A$ is invariant under $\tau_A$, this implies
$\pi_1^{A,A}\equiv\pi_2^{A,A}$.
```

From h_A≡π₁ and h_Aτ_A=h_A, congruence gives π₁τ_A≡π₁; π₁τ_A=π₂, so projections are equivalent.

## C069 — source lines 549–553

```tex
For any parallel arrows $f,g:X\to A$, pairing now gives
\[
 f=\pi_1^{A,A}\circ\langle f,g\rangle
   \equiv\pi_2^{A,A}\circ\langle f,g\rangle=g.
\]
```

f,g:X→A have a pair X→A∧A. The product β laws identify its composites with π₁ and π₂ as f and g; congruence under precomposition with the pair proves f≡g.

## C070 — source lines 554–554

```tex
Thus the quotient is a preorder.
```

The preceding argument covers every target A and every parallel pair with any source X, exactly thinness. Hom-sets that were empty remain empty.

## C071 — source lines 558–559

```tex
Suppose that a substitution congruence $\theta$ on $\B(P)$ identifies
two distinct parallel arrows.
```

This begins proof of the main theorem with its sole nontrivial hypothesis: a substitution congruence properly identifying an original pair. Equality itself and totality are already congruences.

## C072 — source lines 559–560

```tex
Proposition~\ref{prop:all-contexts}
gives \eqref{eq:context} modulo $\theta$ for every formula $A$.
```

Correct invocation of the all-contexts proposition under substitution congruence and nontrivial pair hypotheses.

## C073 — source lines 561–561

```tex
Lemma~\ref{lem:collapse} then makes $\theta$ total.
```

The collapse lemma needs only a proof congruence and all K_A, both furnished above. Thin quotient is equivalent to θ containing every parallel pair.

## C074 — source lines 564–565

```tex
The same argument gives the formulation of maximality in terms of
models used in \cite[\S9.3, p.~194]{DP}.
```

Source §9.3 printed p.194 defines maximality by every natural category satisfying a new equation becoming a preorder. The following corollary instantiates this all-interpretations semantics for the zero-identity Boolean signature.

## C075 — source lines 565–569

```tex
An \emph{interpretation} in
a zero-identity Boolean category $\mathcal C$ assigns an object of
$\mathcal C$ to each propositional variable and interprets the
specified operations; it induces a structure-preserving functor
$\B(P)\to\mathcal C$.
```

Interpretation assigns variables to objects and the specified signature to its given operations in C; initial freeness of B(P) yields the covariant functor, sending formulas to their interpretations and terms to arrow interpretations. Relations in the source presentation hold in a zero-identity Boolean category by definition. This is not an arbitrary functor.

## C076 — source lines 572–573

```tex
Let $P$ be a nonempty set of propositional variables, and let
$f,g:A\to C$ be distinct arrows of $\B(P)$.
```

P nonempty is needed later to choose p and assign its interpretation to any object X. Distinctness furnishes a nontrivial kernel-intersection congruence; parallelism ensures equality is typed.

## C077 — source lines 574–576

```tex
If a zero-identity Boolean category $\mathcal C$ satisfies $f=g$
under every interpretation of the propositional variables, then
$\mathcal C$ is a preorder.
```

The assumption is every object interpretation, not one interpretation. The proof uses the intersection of all kernels to obtain substitution closure and then interprets a chosen variable by every object; its endpoint is thinness of C.

## C078 — source lines 580–581

```tex
Declare two parallel arrows of $\B(P)$ equivalent when all their
interpretations in $\mathcal C$ agree.
```

For each source hom-set, intersection of equivalence kernels gives an equivalence relation. Each interpretation preserves arrow operations, so the intersection is an operation congruence; underlying morphisms with unequal objects are never compared.

## C079 — source lines 581–583

```tex
This defines a substitution
congruence: composing an interpretation with $F_\sigma$ is another
interpretation.
```

For σ:P→Form(P) and any interpretation H:B(P)→C, H∘F_σ is another interpretation. If H′f=H′g for every H′, then taking H′=H∘F_σ proves all H agree on f[σ],g[σ]. This does not incorrectly assert one fixed interpretation kernel is substitution stable.

## C080 — source lines 583–584

```tex
The congruence contains $f=g$, so
Theorem~\ref{thm:main} makes it total.
```

The corollary assumption places the specified distinct f,g in the intersection; the main theorem therefore applies to that substitution congruence.

## C081 — source lines 584–586

```tex
In particular,
$\pi_1^{p,p}=\pi_2^{p,p}$ holds under every interpretation, for any
$p\in P$.
```

Totality applies to the two parallel arrows π₁^{p,p},π₂^{p,p}. The definition of the intersection then says every interpretation makes their images equal.

## C082 — source lines 586–586

```tex
Interpret $p$ as an arbitrary object $X$ of $\mathcal C$.
```

Choose p using nonempty P. An assignment exists for each X: send p to X and all other variables to the terminal object of C; freeness yields its interpretation. C is nonempty since it has top.

## C083 — source lines 587–587

```tex
Its two projections $X\wedge X\to X$ are equal.
```

The chosen interpretation preserves the specified product and projections, so the previous interpreted equality is π₁^{X,X}=π₂^{X,X}.

## C084 — source lines 587–588

```tex
For any arrows $a,b:Y\to X$, composing
$\langle a,b\rangle:Y\to X\wedge X$ with the equal projections gives $a=b$.
```

First form ⟨a,b⟩:Y→X∧X. Composition with the two equal projections gives respectively a and b, hence a=b. Pairing and composition are now distinguished.

Disposition: corrected and rechecked.

## A001 — source lines 591–592

```tex
\appendix
\section{Substitution in occurrence coordinates}\label{app:substitution}
```

Appendix marker and heading describe the occurrence-coordinate construction that follows.

## A002 — source lines 594–596

```tex
The generalized composition of definable connectives in
\cite[\S2.5, pp.~45--46]{DP} records how repeated arguments are
substituted into repeated positions.
```

DP §2.5 pp45–46 defines generalized composition of pairs (skeleton, indexing map), with one inserted copy for every occurrence of an outer argument. The statement is accurate.

## A003 — source lines 596–597

```tex
We give its diagrammatic description
from \cite[\S\S9.2--9.3]{Notation}.
```

Verified full public v8 TeX §§9.2–9.3: it supplies the fibre square and coordinate square used here. This is attribution, not a priority claim.

## A004 — source lines 597–599

```tex
The diagrams separate the choice of
an outer occurrence, the choice of an occurrence within an inserted
formula, and the name assigned to that occurrence.
```

D retains the outer tag r and local occurrence t; gamma and the subsequent renaming retain/assign the name separately.

## A005 — source lines 601–601

```tex
\subsection{Profiles and their fibres}\label{app:profiles}
```

Section contains profiles and their source fibres.

## A006 — source lines 603–604

```tex
For an integer $n\geq0$, put $\underline n=\{1,\ldots,n\}$, with
$\underline0=\varnothing$.
```

This is a one-based finite-ordinal convention with the empty ordinal specified.

## A007 — source lines 604–605

```tex
A \emph{formula pattern} on a finite set
of placeholders is a formula in those placeholders.
```

Definition uses Form already defined for an arbitrary variable set; constants remain allowed even if the placeholder set is empty.

## A008 — source lines 605–607

```tex
Its
\emph{occurrence profile} records the placeholder at each position,
reading positions from left to right.
```

A profile records positions rather than collapsing repeated equal placeholders; formal codomain appears immediately below.

## A009 — source lines 609–610

```tex
Let $U=\{p_1,\ldots,p_k\}$ consist of distinct placeholders and let
$M\in\FormulaSet(U)$ have $m$ occurrences.
```

Distinct enumerated p_i make each occurrence index uniquely identifiable; unused placeholders are permitted.

## A010 — source lines 610–614

```tex
Its profile is
\[
 o_M:\underline m\longrightarrow\underline k,
 \qquad o_M(r)=i\quad\text{when position $r$ contains $p_i$}.
\]
```

Typed o_M: underline(m) -> underline(k); each occurrence has exactly one placeholder index because U is an enumerated set of distinct placeholders. If k=0 then m=0. Display checked.

## A011 — source lines 615–617

```tex
For each $i\in\underline k$, choose a set
$Q_i=\{q_{i,1},\ldots,q_{i,\ell_i}\}$ of distinct local placeholders and a
pattern $N_i\in\FormulaSet(Q_i)$ with $n_i$ occurrences.
```

Each local finite set is separately enumerated without repetitions; n_i may be zero for closed patterns.

## A012 — source lines 617–618

```tex
The sets
$Q_i$ are pairwise disjoint.
```

This is an explicit permissible hypothesis; the later tagging makes the resulting target labels identifiable.

## A013 — source lines 618–619

```tex
Write
$o_i:\underline{n_i}\to\underline{\ell_i}$ for the profile of $N_i$.
```

Typed map o_i from occurrence positions to local placeholder indices; no injectivity or surjectivity assumed.

## A014 — source lines 620–620

```tex
All these numbers may be zero whenever the displayed maps exist.
```

Zero arities/occurrence counts cause no undefined map: an empty placeholder set forces an empty occurrence domain; a positive placeholder set may still have a closed formula with no occurrences.

## A015 — source lines 622–629

```tex
The occurrences after substitution and the local placeholder indices
form, respectively, the sets
\[
 \begin{aligned}
 D&=\{(r,t):r\in\underline m,\ t\in\underline{n_{o_M(r)}}\},\\
 C&=\{(i,s):i\in\underline k,\ s\in\underline{\ell_i}\}.
 \end{aligned}
\]
```

D is a dependent tagged sum indexed by every outer occurrence, with local size n_{o_M(r)}. C is the tagged placeholder-index set, not the set of source occurrences. Both definitions have finite endpoints.

## A016 — source lines 630–631

```tex
Thus $(r,t)$ specifies an occurrence in the copy of $N_{o_M(r)}$
inserted at position $r$ of $M$.
```

This restates the dependent-sum coordinates and correctly uses the outer profile o_M(r).

## A017 — source lines 631–632

```tex
The pair $(i,s)$ specifies a local
placeholder of $N_i$.
```

Membership in C guarantees i in underline(k) and s in underline(l_i). A placeholder may be unused in N_i; the claim does not assert it occurs.

## A018 — source lines 632–637

```tex
Define the injections
\[
 a_r:\underline{n_{o_M(r)}}\longrightarrow D,\quad a_r(t)=(r,t),
 \qquad
 b_i:\underline{\ell_i}\longrightarrow C,\quad b_i(s)=(i,s).
\]
```

a_r and b_i are injective by equality of ordered pairs. Empty-domain injections are still defined. Each target is exactly D or C as declared.

## A019 — source lines 638–646

```tex
There is a unique function $\gamma:D\to C$ for which, for every
$r\in\underline m$, the following square commutes:
\begin{equation}\label{eq:app-fibre}
\begin{tikzcd}[column sep=large,row sep=large]
 \underline{n_{o_M(r)}}\arrow[r,"a_r"]\arrow[d,"o_{o_M(r)}"']
   &D\arrow[d,"\gamma"]\\
 \underline{\ell_{o_M(r)}}\arrow[r,"b_{o_M(r)}"']&C.
\end{tikzcd}
\end{equation}
```

Both paths have domain underline(n_{o_M(r)}) and codomain C. Existence: gamma(r,t)=(o_M(r),o_{o_M(r)}(t)); inner profile has the required codomain. Uniqueness: each (r,t) lies in exactly one a_r image. If D is empty there is exactly one map D->C.

## A020 — source lines 647–649

```tex
The square says that an occurrence inside one inserted copy is labelled
by that pattern's profile and then placed in the corresponding target
block.
```

Lower path computes the local profile then injects into the target block o_M(r); upper path is gamma restricted to the r-th source block.

## A021 — source lines 649–650

```tex
Since $D$ is the disjoint union of its source blocks, these
squares determine $\gamma$ on every element.
```

Disjoint-union coverage yields elementwise uniqueness; no unproved categorical coherence is used.

## A022 — source lines 650–653

```tex
Explicitly,
\[
 \gamma(r,t)=\bigl(o_M(r),o_{o_M(r)}(t)\bigr).
\]
```

gamma(r,t) is well typed because o_{o_M(r)}(t) lies in underline(l_{o_M(r)}); repeated o_M values keep different source tags.

## A023 — source lines 655–656

```tex
Define the block projections $p_D:D\to\underline m$ and
$p_C:C\to\underline k$ by $p_D(r,t)=r$ and $p_C(i,s)=i$.
```

Both maps are total projections from their dependent tagged sums; values lie in the specified finite ordinals.

## A024 — source lines 657–663

```tex
The same construction fits over the outer profile:
\begin{equation}\label{eq:app-profile}
\begin{tikzcd}[column sep=large,row sep=large]
 D\arrow[r,"\gamma"]\arrow[d,"p_D"']&C\arrow[d,"p_C"]\\
 \underline m\arrow[r,"o_M"']&\underline k.
\end{tikzcd}
\end{equation}
```

Both paths D->underline(k) evaluate to o_M(r); the diagram expresses a commuting square of functions, without a pullback claim.

## A025 — source lines 664–664

```tex
Both routes send $(r,t)$ to $o_M(r)$.
```

Direct evaluation: p_C(gamma(r,t))=o_M(r)=o_M(p_D(r,t)).

## A026 — source lines 664–666

```tex
This square records which
inserted pattern is used; square~\eqref{eq:app-fibre} specifies the
map within each such block.
```

The outer square only fixes target tags; the fibre squares also fix local values. The text distinguishes these two amounts of information.

## A027 — source lines 666–668

```tex
Repeated values of $o_M$ give separate
source blocks, one for each occurrence of the corresponding outer
placeholder.
```

The first coordinate of D is occurrence index r, so equal o_M values do not identify different source blocks.

## A028 — source lines 670–672

```tex
To identify this construction with actual pattern substitution,
replace each $q_{i,s}$ in $N_i$ by $(i,s)$ and denote the resulting
pattern over $C$ by $\widetilde N_i$.
```

Each local placeholder q_{i,s} has unique s, so renaming to (i,s) is well defined; the new labels are in C.

## A029 — source lines 672–673

```tex
Let
$\Phi_0:U\to\FormulaSet(C)$ be given by $\Phi_0(p_i)=\widetilde N_i$.
```

p_i are distinct and exhaust U, so this defines a total substitution U->Form(C).

## A030 — source lines 674–674

```tex
Every occurrence of $M[\Phi_0]$ has unique coordinates $(r,t)\in D$.
```

Structural recursion on M: a variable p_i contributes a copy of N_i, constants contribute none, connectives concatenate tags, and negation leaves occurrence sets unchanged. This gives both uniqueness and coverage.

## A031 — source lines 675–683

```tex
This gives a bijection $\chi:\Occ(M[\Phi_0])\to D$, and its relation
to the label map is the commutative square
\begin{equation}\label{eq:app-occurrence-labels}
\begin{tikzcd}[column sep=large,row sep=large]
 \Occ(M[\Phi_0])\arrow[r,"\chi","\cong"']
    \arrow[d,"\lambda_{M[\Phi_0]}"']&D\arrow[d,"\gamma"]\\
 C\arrow[r,"1_C"']&C.
\end{tikzcd}
\end{equation}
```

chi is the structural-recursion bijection just described. Both square paths Occ(M[Phi_0])->C yield the placeholder (o_M(r),o_{o_M(r)}(t)); bottom map is identity_C. Empty domains are harmless.

## A032 — source lines 684–685

```tex
Indeed, the occurrence with coordinates $(r,t)$ contains precisely
the placeholder $\bigl(o_M(r),o_{o_M(r)}(t)\bigr)$.
```

The outer slot picks N_{o_M(r)}, whose local t-th occurrence has index o_{o_M(r)}(t); target renaming appends the selected pattern index.

## A033 — source lines 687–687

```tex
\subsection{The finite-ordinal presentation}\label{app:ordinals}
```

Heading describes the finite-ordinal coordinates used throughout the subsection.

## A034 — source lines 689–690

```tex
The finite ordinals used in \cite{DP} number the elements of each
block consecutively.
```

DP §2.5 p46 uses cumulative source sizes pi and target sizes lambda; these number the concatenated blocks consecutively.

## A035 — source lines 690–695

```tex
Put
\[
 s_0=t_0=0,\qquad
 s_r=\sum_{q=1}^{r}n_{o_M(q)}\quad(1\leq r\leq m),\qquad
 t_i=\sum_{j=1}^{i}\ell_j\quad(1\leq i\leq k).
\]
```

s_r counts source occurrences through outer position r, including repeated selections; t_i counts target placeholders through pattern i. Zero base values make r=1 and i=1 offsets defined.

## A036 — source lines 696–704

```tex
The block encodings are the bijections
\[
 \begin{aligned}
 \theta_D:D&\longrightarrow\underline{s_m},
       &\theta_D(r,t)&=s_{r-1}+t,\\
 \theta_C:C&\longrightarrow\underline{t_k},
       &\theta_C(i,s)&=t_{i-1}+s.
 \end{aligned}
\]
```

Each map adds the cumulative size of preceding blocks. For x in the source ordinal, the unique r satisfying s_{r-1}<x<=s_r determines t=x-s_{r-1}; the analogous inverse gives target coordinates. Empty blocks cannot contain a position; when the total is zero the unique empty function is bijective.

## A037 — source lines 705–713

```tex
Define $\delta:\underline{s_m}\to\underline{t_k}$ as the unique
function making the following square commute:
\begin{equation}\label{eq:app-ordinal}
\begin{tikzcd}[column sep=large,row sep=large]
 D\arrow[r,"\gamma"]\arrow[d,"\theta_D","\cong"']
    &C\arrow[d,"\theta_C","\cong"']\\
 \underline{s_m}\arrow[r,"\delta"']&\underline{t_k}.
\end{tikzcd}
\end{equation}
```

Existence and uniqueness follow from delta=theta_C o gamma o theta_D^{-1}; all three maps are typed. The inverse is only used for a proven bijection, and empty-total cases still work.

## A038 — source lines 714–714

```tex
The vertical maps change coordinates.
```

Both vertical arrows are exactly the declared block encodings; they are not substitutions or identifications of occurrences.

## A039 — source lines 714–716

```tex
The top route keeps the block
and local position visible; the bottom route uses a single position
number.
```

The top horizontal map gamma uses tagged coordinates (r,t); the bottom horizontal map delta operates on encoded ordinals. This is consistent with the full square.

## A040 — source lines 716–720

```tex
In coordinates, commutativity says
\begin{equation}\label{eq:app-coordinate}
 \delta(s_{r-1}+t)=t_{o_M(r)-1}+o_{o_M(r)}(t)
 \qquad\bigl((r,t)\in D\bigr).
\end{equation}
```

At (r,t), theta_D gives s_{r-1}+t; theta_C(gamma(r,t)) gives t_{o_M(r)-1}+o_{o_M(r)}(t). Indices are in range since o_M(r)>=1.

## A041 — source lines 721–722

```tex
Every source position belongs to exactly one nonempty block, so this
formula determines $\delta$ even when some blocks are empty.
```

Positive x has a unique least r with x<=s_r; necessarily s_{r-1}<x and n_{o_M(r)}>0. All-zero source admits the unique empty function. No positive-source/empty-target case can occur because then a required local profile would be impossible.

## A042 — source lines 724–725

```tex
In Do\v{s}en and Petri\'c's notation, $\mu$ and $\nu_i$ correspond to
$o_M$ and $o_i$, and $\mu(\nu_1,\ldots,\nu_k)$ corresponds to $\delta$.
```

The manuscript identifies its o_M,o_i,δ with the source symbols μ,ν_i,μ(ν₁,…,ν_k); it no longer attributes its own symbols to the source.

Disposition: corrected and rechecked.

## A043 — source lines 726–729

```tex
Their block locator selects the unique $r$ for which
$s_{r-1}<x\leq s_r$; substituting $t=x-s_{r-1}$ in
\eqref{eq:app-coordinate} gives their formula
\cite[\S2.5, p.~46]{DP}.
```

Substitute t=x−s_(r−1) in δ(s_(r−1)+t)=t_(o_M(r)−1)+o_(o_M(r))(t). The result is the source block-locator formula on printed p.46.

Disposition: corrected and rechecked.

## A044 — source lines 729–730

```tex
The square therefore describes the
occurrence-profile component of their generalized composition.
```

The square computes the occurrence-profile component δ. The next two sentences separately account for the substituted skeleton needed to specify the full generalized composite.

Disposition: corrected and rechecked.

## A045 — source lines 731–732

```tex
A pattern can equivalently be specified by erasing its placeholder names to one common symbol and
attaching its occurrence profile.
```

Given the fixed ordered placeholder set, the erased syntax tree plus profile reconstructs the original variable at each leaf. Constants and connective symbols remain. The same statement works with zero variable occurrences.

## A046 — source lines 732–734

```tex
In that notation, the generalized
composite is represented by the skeleton of the substituted pattern
together with the profile $\delta$.
```

DP p46 defines the result as M(N_{mu(1)},...,N_{mu(m)}) decorated by mu(nu_1,...,nu_k). The manuscript now correctly says skeleton of the substituted pattern; previous review’s skeleton/label confusion is repaired.

## A047 — source lines 736–741

```tex
For example, take
\[
 M(p,q)=q\wedge(p\vee q),\qquad
 N_1(a,b)=a\wedge b,\qquad
 N_2(c,d)=d\wedge(c\vee d).
\]
```

All three finite patterns are well formed with distinct formal placeholder lists; their displayed syntax fixes the left-to-right leaf order.

## A048 — source lines 742–743

```tex
The profiles, listed by successive values, are
$o_M=(2,1,2)$, $o_1=(1,2)$, and $o_2=(2,1,2)$.
```

Reading M gives q,p,q; N1 gives a,b; N2 gives d,c,d. Indices are therefore exactly as stated.

## A049 — source lines 744–745

```tex
The source blocks have sizes $3,2,3$, while the target blocks list
$(a,b)$ and $(c,d)$.
```

Outer q,p,q selects N2,N1,N2, of sizes3,2,3. Target placeholder blocks retain distinct a,b and c,d.

## A050 — source lines 745–752

```tex
Thus
\[
\begin{array}{c|ccc|cc|ccc}
 \text{source position}&1&2&3&4&5&6&7&8\\\hline
 \text{placeholder}&d&c&d&a&b&d&c&d\\
 \delta&4&3&4&1&2&4&3&4
\end{array}
\]
```

Explicit substitution yields d,c,d,a,b,d,c,d. Target codes a=1,b=2,c=3,d=4 give 4,3,4,1,2,4,3,4. Repeated source letters remain separate entries.

## A051 — source lines 753–753

```tex
For instance, source position $2$ has coordinates $(1,2)$.
```

Source offsets are s0=0,s1=3,s2=5,s3=8; x=2 lies in block1 with local t=2.

## A052 — source lines 754–755

```tex
The profile map gives $\gamma(1,2)=(2,1)$, and the target encoding
then gives $\theta_C(2,1)=3$.
```

The explicit map γ sends the coordinate pair (1,2) to (2,1); θ_C then sends (2,1) to3. A diagram itself is no longer called a function.

Disposition: corrected and rechecked.

## A053 — source lines 755–755

```tex
Thus $\delta(2)=3$.
```

The composition of the two explicitly calculated coordinate maps gives δ(2)=3, agreeing with the displayed example table.

Disposition: corrected and rechecked.

## A054 — source lines 757–757

```tex
\subsection{Shared variables and the maximality argument}\label{app:shared}
```

Heading describes renaming shared variables and the single-occurrence application.

## A055 — source lines 759–760

```tex
The local placeholders may be assigned names in a common variable
set $Q$.
```

This introduces the possibility of a name assignment; the next sentence explicitly assumes such a map. No existence is asserted for a nonempty C and empty Q without an assignment.

## A056 — source lines 760–761

```tex
Let $\rho:C\to Q$ be that assignment; different elements
of $C$ may have the same image.
```

rho:C->Q is a declared total function, not assumed injective; this is needed to represent repeated shared variables.

## A057 — source lines 761–763

```tex
Replace each placeholder $c\in C$
by the variable $\rho(c)$, obtaining the renaming map
$(-)[\rho]:\FormulaSet(C)\to\FormulaSet(Q)$.
```

Structural recursion sends each c to the variable rho(c), fixes constants and preserves connectives. Domain/codomain correct even with empty variable sets whenever rho exists.

## A058 — source lines 763–765

```tex
Define
$\sigma:U\to\FormulaSet(Q)$ by
$\sigma(p_i)=\widetilde N_i[\rho]$.
```

Phi0(p_i) belongs to Form(C); renaming produces Form(Q). The distinct p_i exhaust U, so sigma is well defined.

## A059 — source lines 766–774

```tex
Then the following square commutes:
\begin{equation}\label{eq:app-renaming}
\begin{tikzcd}[column sep=large,row sep=large]
 \FormulaSet(U)\arrow[r,"{(-)[\Phi_0]}"]
    \arrow[d,"{(-)[\sigma]}"']
   &\FormulaSet(C)\arrow[d,"{(-)[\rho]}"]\\
 \FormulaSet(Q)\arrow[r,"1"']&\FormulaSet(Q).
\end{tikzcd}
\end{equation}
```

For M:Form(U), both routes evaluate to M[sigma]=M[Phi0][rho]. Variable clause uses sigma definition; constants and each connective agree recursively. Bottom identity has source/target Form(Q).

## A060 — source lines 775–775

```tex
At $p_i$, both routes give $\sigma(p_i)$.
```

Upper-right route is tildeN_i[rho]; lower-left route is sigma(p_i), equal by definition.

## A061 — source lines 775–776

```tex
The constant and connective
clauses agree, so structural induction proves commutativity.
```

Constants fixed by both substitutions; each unary/binary connective is preserved by each route. These are all constructors of Form.

## A062 — source lines 777–778

```tex
Renaming changes the labels on the occurrences, while the pairs
$(r,t)$ continue to distinguish their positions.
```

A variable renaming changes leaf names only; syntax-tree positions and ordered block tags are untouched.

## A063 — source lines 778–780

```tex
This permits the
same actual variable to occur in several inserted patterns without
identifying their separate occurrences.
```

Noninjective rho can identify labels from different C blocks while the occurrence domain D remains unchanged. No relation between labels is promoted to equality of occurrences.

## A064 — source lines 782–784

```tex
For the substitution $p\mapsto A$ in
Proposition~\ref{prop:all-contexts}, the outer pattern is $p$,
so there is a single source block.
```

For the isolated literal variable p, the profile has one slot. The actual source and target contexts are then discussed explicitly, so the sentence does not confuse those formulas with the outer placeholder.

## A065 — source lines 784–784

```tex
This block is $\Occ(A)$.
```

In the manuscript’s tagged occurrence convention Eq(4), one inserted occurrence block is Occ(A); finite-ordinal coding of it is only a change of coordinates.

## A066 — source lines 785–786

```tex
The source and target formulas of the contextual equation are
$p\wedge\bot$ and $p\vee\top$; each has one occurrence of $p$.
```

Constants contribute no variable occurrences. Both named formulas thus have one variable slot.

## A067 — source lines 786–788

```tex
Their substituted occurrence sets therefore each
contain one copy of $\Occ(A)$, and the substituted arrow has type
$A\wedge\bot\to A\vee\top$.
```

Uniform whole-arrow substitution sends the endpoints exactly as stated; Occ(bot)=Occ(top)=empty, so both endpoint occurrence sets have one tagged copy of Occ(A), including when that set is empty.

## A068 — source lines 788–792

```tex
If the isolated literal is $\neg p$,
the substitution $p\mapsto\neg A$ instead gives
$\neg\neg A\wedge\bot\to\neg\neg A\vee\top$; the
double-negation square in Proposition~\ref{prop:all-contexts}
then gives the required equation for $A$.
```

Substitution p->neg A sends neg p to neg neg A. Precompose by n_A^{-1} tensor id_bot and postcompose by n_A coproduct id_top; the declared double-negation isomorphism and zero absorption yield K_A. Types match the main-text square.

## O51 — source lines 794–795

```tex
\section{Diagrammatic forms of the structural equations}
\label{app:structural-diagrams}
```

Appendix heading is accurate: it gives diagrams for the equations introduced as structural data in §2.

## O52 — source lines 797–797

```tex
\paragraph{The first-injection equation.}
```

Heading identifies the existing equation (1).

## O53 — source lines 798–808

```tex
For formulas $A,B,C$, equation~\eqref{eq:first-injection} is the
commutative triangle
\[
\begin{tikzcd}[column sep=large,row sep=large]
 A\wedge B
   \arrow[r,"1_A\wedge\iota_1^{B,C}"]
   \arrow[dr,"{\iota_1^{A\wedge B,C}}"']
   &A\wedge(B\vee C)\arrow[d,"d_{A,B,C}"]\\
   &(A\wedge B)\vee C.
\end{tikzcd}
\]
```

The triangle has A∧B→A∧(B∨C) via 1_A∧ι1 and A∧(B∨C)→(A∧B)∨C via d, compared with ι1:A∧B→(A∧B)∨C. Its asserted commutativity is exactly (1), not an additional theorem.

## O54 — source lines 809–809

```tex
Both paths have source $A\wedge B$ and target $(A\wedge B)\vee C$.
```

Checked the product bifunctor endpoint of 1_A∧ι1 and d endpoint; the direct injection has those same endpoints.

## O55 — source lines 810–811

```tex
The upper arrow is induced by $1_A:A\to A$ and
$\iota_1^{B,C}:B\to B\vee C$.
```

Product action on these two arrows has source A∧B and target A∧(B∨C), exactly the horizontal arrow.

## O56 — source lines 813–813

```tex
\paragraph{The zero identity.}
```

Heading identifies the endomorphism defined by equation (2).

## O57 — source lines 814–825

```tex
For a formula $A$, equation~\eqref{eq:zero-identity} is expressed by
the commutative diagram
\[
\begin{tikzcd}[column sep=large,row sep=large]
 A\arrow[r,"{\langle1_A,!_A\rangle}"]\arrow[d,"0_A"']
   &A\wedge\top\arrow[r,"1_A\wedge\eta_A"]
   &A\wedge(\neg A\vee A)\arrow[d,"d_{A,\neg A,A}"]\\
 A
   &\bot\vee A\arrow[l,"{[\kappa_A,1_A]}"']
   &(A\wedge\neg A)\vee A\arrow[l,"\epsilon_A\vee1_A"'].
\end{tikzcd}
\]
```

All five composite arrows are typed in sequence: A→A∧top→A∧(neg A∨A)→(A∧neg A)∨A→bot∨A→A. The separate arrow 0_A:A→A is parallel to that path. The diagram states equation (2), which DP calls (0ηε), printed p317.

## O58 — source lines 826–827

```tex
The path across the top, down the right side, and back along the
bottom is the five-arrow composite in~\eqref{eq:zero-identity}.
```

Reading the diagram in the stated order yields pairing, 1∧eta, d, epsilon∨1, copairing. Algebraic composition in (2) lists those five in reverse evaluation order, as §2 explicitly stipulates.

## O59 — source lines 828–829

```tex
Its first arrow pairs $1_A:A\to A$ with $!_A:A\to\top$;
its last arrow copairs $\kappa_A:\bot\to A$ with $1_A:A\to A$.
```

Both pairing components share domain A, giving A→A∧top; both copairing components share codomain A, giving bot∨A→A. Operational first/last refer to the immediately preceding path description.

## O60 — source lines 830–832

```tex
The arrows between them use
$\eta_A:\top\to\neg A\vee A$ and
$\epsilon_A:A\wedge\neg A\to\bot$, together with the distributor.
```

The three interior arrows are their indicated tensors with identity and d_{A,neg A,A}; the supplied types ensure all intermediate composites exist.

## O61 — source lines 834–834

```tex
\paragraph{The zero law.}
```

Heading identifies equation (3), the zero law.

## O62 — source lines 835–842

```tex
For any parallel arrows $f,g:A\to C$,
equation~\eqref{eq:zero-law} is the commutative square
\[
\begin{tikzcd}[column sep=large,row sep=large]
 A\arrow[r,"0_A"]\arrow[d,"g"']&A\arrow[d,"f"]\\
 C\arrow[r,"0_C"']&C.
\end{tikzcd}
\]
```

Square endpoints: top 0_A:A→A, right f:A→C, left g:A→C, bottom 0_C:C→C. Both paths have type A→C. Its commutativity is precisely f∘0_A=0_C∘g; no equality of f and g is assumed.

## O63 — source lines 843–844

```tex
The upper-right path is $f\circ0_A:A\to C$, and the lower-left
path is $0_C\circ g:A\to C$.
```

Composite order agrees with the declared convention (rightmost first) and with the actual drawn paths.

## O64 — source lines 844–844

```tex
The arrows $f$ and $g$ need not be equal.
```

Equation (3) quantifies over independent parallel arrows. For A=p∧p and C=p, distinct projections supply an actual unequal example in B, so this is more than a vacuous observation.

## F075 — source lines 846–846

```tex
\paragraph{Use of AI tools.}
```

Conventional disclosure heading, not a mathematical claim.

## F076 — source lines 847–848

```tex
OpenAI's ChatGPT was used to assist with the development of the proof,
preparation of the manuscript, and checks of the arguments and references.
```

Disclosure accurately reflects author-side tool-assisted proof/manuscript/reference work documented in this conversation; no independent peer-review claim.

## F077 — source lines 855–860

```tex
\bibitem{DP}
Kosta Do\v{s}en and Zoran Petri\'c,
\emph{Proof-Theoretical Coherence},
Studies in Logic, vol.~1, King's College Publications, London, 2004.
Revised author version, September 2007.
\url{https://www.mi.sanu.ac.rs/novi_sajt/biography/kosta/coh.pdf}.
```

The publisher is spelled King's College Publications, matching the author's publication record. The September 2007 revision and its URL are retained.

Disposition: corrected and rechecked.

## F078 — source lines 862–866

```tex
\bibitem{DPCartesian}
Kosta Do\v{s}en and Zoran Petri\'c,
The maximality of cartesian categories,
\emph{Mathematical Logic Quarterly} \textbf{47} (2001), 137--144.
\url{https://arxiv.org/abs/math/9911059}.
```

Full supplied preprint title/author; official DP publication list paper54 confirms MLQ47(2001),137–144 and arXiv9911059.

## F079 — source lines 868–874

```tex
\bibitem{DPBicartesian}
Kosta Do\v{s}en and Zoran Petri\'c,
Bicartesian coherence revisited,
in Zoran Ognjanovi\'c (ed.), \emph{Logic in Computer Science},
Zbornik radova \textbf{12(20)} (2009), 5--34.
\url{https://arxiv.org/abs/0711.4961}.
Author version: arXiv:0711.4961v3, December 8, 2008.
```

Full arXiv0711.4961v3 dated8Dec2008; official DP publication list paper78 confirms Ognjanović(ed.),Logic in Computer Science,Zbornik radova12(20)(2009),5–34.

## F080 — source lines 876–882

```tex
\bibitem{DPIsomorphic}
Kosta Do\v{s}en and Zoran Petri\'c,
Isomorphic formulae in classical propositional logic,
\emph{Mathematical Logic Quarterly} \textbf{58} (2012), 5--17.
\url{https://doi.org/10.1002/malq.201020020}.
Author version: \url{https://arxiv.org/abs/0912.1271},
arXiv:0912.1271v3, October 4, 2010.
```

Full arXiv0912.1271v3 dated4Oct2010; official DP publication list paper86 confirms MLQ58(2012),5–17. DOI agrees with publisher indexing.

## F081 — source lines 884–889

```tex
\bibitem{DPSplit}
Kosta Do\v{s}en and Zoran Petri\'c,
Syntax for split preorders,
\emph{Annals of Pure and Applied Logic} \textbf{164} (2013), 443--481.
\url{https://arxiv.org/abs/0902.0742}.
Author version: arXiv:0902.0742v7, October 18, 2012.
```

Full arXiv0902.0742v7 dated18Oct2012; official DP publication list paper89 confirms APAL164(2013),443–481.

## F082 — source lines 891–896

```tex
\bibitem{LSFree}
Fran\c{c}ois Lamarche and Lutz Stra{\ss}burger,
Constructing free Boolean categories,
in \emph{Proceedings of the 20th Annual IEEE Symposium on Logic in
Computer Science (LICS 2005)}, IEEE Computer Society, 2005, pp.~209--218.
\url{https://doi.org/10.1109/LICS.2005.13}.
```

Supplied full LS PDF HAL cover supplies authors,title,LICS2005,209–218, DOI10.1109/LICS.2005.13.

## F083 — source lines 898–902

```tex
\bibitem{FP}
Carsten F\"uhrmann and David Pym,
Order-enriched categorical models of the classical sequent calculus,
\emph{Journal of Pure and Applied Algebra} \textbf{204} (2006), 21--78.
\url{https://doi.org/10.1016/j.jpaa.2005.03.016}.
```

Supplied full FP journal PDF first-page metadata/header confirms JPAA204(2006),21–78 and DOI.

## F084 — source lines 904–909

```tex
\bibitem{Strassburger}
Lutz Stra{\ss}burger,
On the axiomatisation of Boolean categories with and without medial,
\emph{Theory and Applications of Categories} \textbf{18} (2007),
536--601.
\url{https://www.tac.mta.ca/tac/volumes/18/18/18-18abs.html}.
```

TAC official article page confirms author,title,vol18(2007),pp536–601; full arXivcs/0512086v3 available and consulted for content.

## F085 — source lines 911–915

```tex
\bibitem{Notation}
Florian Lengyel,
\emph{The Unbearable Notation of Logic},
version~8, September 19, 2026, Section~9.
\url{https://github.com/flengyel/notes/blob/main/logic/The-Unbearable-Notation-of-Logic_v8.pdf}.
```

Exact author-provided public URL preserved without inserted display punctuation. Occurrence reviewer directly read public Notes v8 TeX from GitHub: title, author and \date{September19,2026} verified; §9 occurrence-indexed substitution, §§9.2–9.3 profiles/ordinal composition checked. File version is in path; no internal version command.
