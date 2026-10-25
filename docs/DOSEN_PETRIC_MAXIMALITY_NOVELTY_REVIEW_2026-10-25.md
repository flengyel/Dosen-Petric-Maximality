# Novelty review: Maximality of the Došen–Petrić Boolean Category

Review date: 25 October 2026. Assessment corrected after an independent subsumption and Lean-scope recheck on the same date.

Manuscript reviewed: Florian Lengyel, *Maximality of the Došen–Petrić Boolean Category*, v5, dated 23 October 2026; source at repository commit `0af6a0e83fdcbb5ec3d98103cbb36b8f2b30dec6`. Source SHA-256: `50f92e84c8ccc5a14e8e403b89f4dbd68e798bacce32dd57f40f990de7d06de7`.

## 1. Assessment

**No earlier explicit statement of the exact Boolean maximality theorem was located. Published structural isomorphisms give a shorter proof of contextual collapse; this does not establish that the maximality theorem was already known or that earlier work subsumes the contribution.** The most consequential comparison is with Došen and Petrić’s isomorphism results, not with Joyal.

The contribution includes connecting the published structural isomorphisms to collapse under an added contextual equation, and applying that collapse to arbitrary new Boolean arrow equations. The conclusion contradicts the book’s nonmaximality conjecture. The symmetric distributor construction and general occurrence-selection method have earlier sources and require attribution. The short derivation below establishes dependence on those inputs; it is not evidence of a prior statement of the theorem, nor a basis for ranking its mathematical significance below the formalization.

The findings have different strengths:

| Question | Finding |
|---|---|
| Is this Joyal’s collapse theorem under another name? | No. Cartesian closure fails in the category under study. |
| Does a checked earlier paper explicitly announce maximality of the same free zero-identity Boolean category? | None located. |
| Can published results substantially shorten the main argument? | Yes. Two advertised isomorphisms yield contextual collapse; the 2012 isomorphism paper supplies an independent route. |
| Is the map called \(h_A\) a new construction? | No. It is the established mix map followed by the codiagonal. |
| Do Petrić’s later coherence papers settle the conjecture directly? | No such statement was found. Several prove coherence or maximality in other signatures. |
| What should change in the manuscript’s positioning? | Credit the old structural inputs and state the new maximality conclusion directly. Do not infer prior publication or diminished significance from a shorter proof. |
| Is the Lean development already an unconditional formalization of the target theorem? | No. It proves relative maximality with explicit inputs; faithfulness for the actual source quotient remains unproved. |

## 2. Exact theorem being compared

The subject is the free **zero-identity** Došen–Petrić Boolean category \(\mathsf B(P)\), with \(P\ne\varnothing\). Its operations include finite products and coproducts, a weak distributor

\[
d_{A,B,C}:A\wedge(B\vee C)\longrightarrow(A\wedge B)\vee C,
\]

involutive negation with the specified structural maps, and zero identities. A zero arrow \(0_{A,C}\) is available when the hom-set \(\mathsf B(A,C)\) is inhabited. There is no assumption of an arrow between every pair of objects.

The theorem classifies congruences on parallel arrows that preserve the proof operations **and uniform substitution for propositional variables**: any such congruence identifying two distinct arrows identifies all parallel arrows. It does not say that every individual model of classical logic is thin, that every ordinary categorical congruence is total, or that all notions called “Boolean category” have this property.

The faithful occurrence functor is used before quotienting to establish equations in the original category. Its faithfulness is not asserted for a nontrivial quotient. These distinctions matter in every comparison below.

## 3. Joyal, Freyd, and related collapse theorems

### 3.1 What the classical theorem assumes

In its standard formulation, Joyal’s lemma says that a cartesian closed category with a dualizing object is a preorder. Here duality is supplied by the closed structure: the canonical map

\[
A\longrightarrow((A\Rightarrow D)\Rightarrow D)
\]

is invertible. See Abramsky, *No-Cloning in Categorical Quantum Mechanics*, Proposition 1, author-version p.5 ([full text](https://arxiv.org/pdf/0910.2401)); the publisher’s formulation is Proposition 1.2.1, p.5 ([excerpt](https://assets.cambridge.org/97805215/13746/excerpt/9780521513746_excerpt.pdf)).

The historical attribution is an oral communication recorded by Lambek and Scott, *Introduction to Higher Order Categorical Logic*, Part I §8, Proposition 8.3, p.67, and historical comments p.116. Their uniqueness result for arrows into an initial object follows Freyd’s strict-initial argument. Freyd, *Aspects of topoi* (1972), Propositions 1.11–1.12, p.7, explains the role of the product–exponential adjunction ([publisher PDF](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/B65FB15DCD85C816F31D9C87D355AD24/S0004972700044828a.pdf/aspects-of-topoi.pdf)). No original published Joyal manuscript was located.

Došen’s *Identity of Proofs Based on Normalization and Generality*, §5, Propositions 1–3, pp.17–18, includes stronger natural/dinatural variants: natural double-negation elimination, or dinatural excluded middle, can suffice **with the appropriate closed structure** ([author text](https://arxiv.org/pdf/math/0208094)). Crolard’s *Subtractive Logic*, Theorem 1.3.3, author-version p.6, shows that a category which is both cartesian closed and cocartesian closed is a preorder ([author text](https://cedric.cnam.fr/sys/crolard/publications/tcs.pdf)). None removes the relevant closure requirement in a way applicable here.

### 3.2 A concrete obstruction in this manuscript

The following is an independent calculation from the manuscript’s assumptions.

For every object \(E\),

\[
|\mathsf B(\top,E)|\le 1,
\]

because every such arrow has the unique relation from the empty occurrence set. On the other hand, \(1_p\ne0_p\): their relations are the singleton diagonal and the empty relation. An exponential \(p\Rightarrow p\) would give

\[
\mathsf B(p,p)\cong\mathsf B(\top,p\Rightarrow p),
\]

which is impossible. Thus \(\mathsf B\) is not cartesian closed, regardless of which formula one proposes for implication.

The strict-initial step fails concretely as well. Put \(X=p\wedge\bot\). The projection \(X\to\bot\) exists, but \(X\) is not initial: \(1_X\) and \(\kappa_X\pi_2:X\to X\) have nonempty and empty relations. In a cartesian closed category, product with \(p\) would preserve the initial object.

Consequently there is no faithful functor from \(\mathsf B\) into a cartesian closed category that preserves both its products and its initial object. A product-preserving Yoneda embedding does not overcome this obstruction: it does not preserve all the structure relevant to the Boolean equation.

A quotient still has at most one global arrow into each object. If that quotient were cartesian closed, the exponential adjunction would already imply its thinness. A proposed Joyal proof must therefore establish the substantial missing closure property; it cannot simply assume it.

### 3.3 Stronger no-go theorems and a tensor distinction

Abramsky’s Theorem 11, p.22, assumes compact closure and a monoidal natural copying operation and obtains scalar collapse of endomorphisms. Proposition 15, p.29, gives preorder under compact closure and uniform deletion. Those hypotheses must concern the same tensor.

Finite relations illustrate why mixing structures is invalid. Their categorical product is disjoint union; their usual compact tensor is set-theoretic product. The ordinary copying relation for the latter is not natural for arbitrary relations: a relation taking one input to two outputs produces cross-pairs on one side of the naturality equation but not the other. Neither compactness nor that naturality follows for the manuscript’s product from the occurrence interpretation.

**Comparison:** the manuscript does not refute Joyal or extend his theorem by merely weakening a named hypothesis. It studies substitution-stable quotients of a different, nonclosed category.

## 4. The decisive prior structure: a short collapse proof

### 4.1 Published inputs

In the September 2007 revision of *Proof-Theoretical Coherence*, §12.5, printed p.294, Došen and Petrić list the isomorphism types

\[
(A\wedge\bot)\vee\top\cong A\vee\top,
\qquad
p^n\wedge(p^m\vee\top)\cong p^{n+m}.
\]

Here \(p^n\) denotes any positive one-letter formula with \(n\) occurrences. Their coherence and relative-maximality results appear on pp.291–292. The conjecture about \(\mathsf B\) is on p.322. [Primary book](https://www.mi.sanu.ac.rs/novi_sajt/biography/kosta/coh.pdf).

The later paper *Isomorphic Formulae in Classical Propositional Logic* (2012; arXiv v3, 4 October 2010), §4, Lemma 7 and Proposition 3, p.13, is especially relevant. The proof of Lemma 7 realizes each same-letter occurrence bijection between classically equivalent positive formulas and constructs an inverse. Thus coherence identifies a given arrow with that isomorphism when it has the chosen bijective relation. This is stronger evidence than an unspecified assertion that the objects happen to be isomorphic. [Primary text](https://arxiv.org/pdf/0912.1271).

The argument that follows is assembled in this review. It is **not** attributed as a theorem stated in either source.

### 4.2 Typed derivation

Fix \(p\in P\), and write

\[
D=p\wedge\bot,\quad E=p\vee\top,\quad S=D\vee\top,
\quad X=p\wedge E.
\]

Set

\[
\begin{aligned}
j&=\iota_1^{p,\top}:p\to E,&
s&=\iota_2^{p,\top}:\top\to E,\\
k&=j\pi_1^{p,\bot}:D\to E,&
q&=[k,s]:S\to E,\\
e&=1_p\wedge j:p\wedge p\to X.
\end{aligned}
\]

**First, \(q\) and \(e\) are isomorphisms in the original category.** The first displayed published isomorphism has the type of \(q\). Its source and target have one occurrence each, so its relational image is the unique singleton bijection. That is also \(Gq\), and faithfulness identifies the two arrows.

For \(e\), take \(n=m=1\) in the second isomorphism and choose \(p^2=p\wedge p\). Its inverse has the type of \(e\). Its relation is one of two permutations. If necessary, precompose with the actual product symmetry on \(p\wedge p\) to obtain the order-preserving bijection \(Ge\). Faithfulness again identifies the arrows. This argument uses no fullness of \(G\).

Alternatively, both claims follow directly from the proof of Lemma 7 in the 2012 paper: the respective endpoint formulas are classically equivalent, and the relations of \(q\) and \(e\) are occurrence bijections.

Now suppose a substitution congruence satisfies the contextual equation

\[
(K_p)\qquad k\equiv0_{D,E}.
\]

In the original category, \(0_{D,E}=s!_D\), since both existing arrows have empty occurrence relation. Thus

\[
q=[k,s]\equiv[s!_D,s]=s!_S.
\]

The second equality is a coproduct equation. The inverse of \(q\) survives in the quotient, whence

\[
1_E=q q^{-1}\equiv s!_S q^{-1}=s!_E.
\]

Since \(!_E s=1_\top\), the object \(E\) is terminal in the quotient. Therefore

\[
r=\pi_1^{p,E}:X\to p
\]

is an isomorphism. Because \(e\) remains invertible and

\[
re=\pi_1^{p,p},
\]

the first projection \(\pi_1^{p,p}\) is invertible. Its right inverse is the diagonal \(\Delta_p\), so \(\Delta_p\pi_1=1_{p\wedge p}\). Hence

\[
\pi_2=\pi_2\Delta_p\pi_1=\pi_1.
\]

Uniform substitution gives \(\pi_1^{A,A}\equiv\pi_2^{A,A}\) for every formula \(A\). For parallel \(f,g:Y\to A\), pairing then gives

\[
f=\pi_1\langle f,g\rangle\equiv\pi_2\langle f,g\rangle=g.
\]

This proves collapse from \(K_p\). No arbitrary zero arrow, quotient faithfulness, or new closed structure has been used.

### 4.3 Explicit inverse terms as an independent check

The isomorphisms can also be verified without relying on the existential assertions on p.294. For arbitrary \(A\), define \(D_A,E_A,S_A,X_A,j_A,s_A,q_A,e_A\) as above with \(p\) replaced by \(A\). Put

\[
v_A=d_{A,\bot,\top}(1_A\wedge\iota_2^{\bot,\top})
\langle1_A,!_A\rangle:A\to S_A.
\]

Then

\[
q_A^{-1}=[v_A,\iota_2^{D_A,\top}]:E_A\to S_A.
\]

Let \(c_A:E_A\to\top\vee A\) be coproduct symmetry, and put

\[
z_A=[\pi_1^{A,\top},1_A]d_{A,\top,A}(0_A\wedge c_A):X_A\to A.
\]

Then

\[
e_A^{-1}=\langle\pi_1^{A,E_A},z_A\rangle:X_A\to A\wedge A.
\]

The relation of \(v_A\) preserves the sole \(A\) block; that of \(z_A\) deletes the first \(A\) block and preserves the second. The two displayed candidate inverses therefore have precisely the inverse occurrence bijections. Coherence proves both inverse equations in each case. These calculations independently verify the structural claims used above.

### 4.4 What this says about novelty

The positive relative-maximality result, combined with this calculation, upgrades to full maximality of the positive zero-identity distributive category with constants. For \(\mathsf B\), the manuscript’s signed-literal normalization and contextual isolation still provide the passage from an arbitrary new Boolean equation to \(K_p\) or its uniformly substitutable version. That passage must be proved; merely containing a maximal positive subcategory would not suffice.

The earlier results therefore supply a short route to the theorem. They do not supply a located prior statement claiming the theorem. Those are different conclusions about priority.

## 5. The manuscript’s symmetric map is established mix structure

Write \(\nabla_A=[1_A,1_A]:A\vee A\to A\). Equation (dm), *Proof-Theoretical Coherence*, §11.1, p.234, gives the parameter-independent mix expression

\[
m_{A,C}=(\pi_1^{A,B}\vee1_C)d_{A,B,C}
(1_A\wedge\iota_2^{B,C}).
\]

Consequently the manuscript’s map is

\[
h_A^B=\nabla_A m_{A,A}.
\]

Its independence of \(B\) is already encoded by (dm). Mix symmetry followed by codiagonal symmetry gives \(h_A\tau_A=h_A\). The map, its independence, and its symmetry are thus prior structure. The manuscript’s proof of them by coherence is valid, but the construction should be attributed at that level. Re-proving a known identity for a self-contained argument is reasonable; treating it as a new mechanism would be misleading.

## 6. Petrić’s later papers: exact comparisons

Dates below distinguish publication from the version actually examined. Page references are to the linked author version unless a journal page is specified.

| Work | Result checked | Consequence for the manuscript |
|---|---|---|
| [Bicartesian Coherence Revisited](https://arxiv.org/pdf/0711.4961), published 2009; v3 December 2008 | §§8–10; the contextual equation and contextual preorder on pp.29–30 | Direct antecedent for occurrence isolation. Its nonmaximality result concerns dicartesian categories without distribution. It does not refute maximality after adding the distributor and zero-identity structure. |
| [Isomorphic Formulae in Classical Propositional Logic](https://arxiv.org/pdf/0912.1271), published 2012; v3 October 2010 | Lemma 7’s proof and Proposition 3, p.13 | The most consequential later source: it supplies the specific inverses needed in §4 above. The current manuscript cites Lemma 6, but the relevance extends beyond occurrence selection. |
| [Syntax for Split Preorders](https://arxiv.org/pdf/0902.0742), published 2013; v7 October 2012 | §16, pp.55–58: maximality of PF, EF, RB | Genuine prior maximality and differing-edge selection. RB’s direct singleton selectors exist in its own relational presentation. Boolean coherence alone does not transfer its maximality theorem. |
| [Coherence for Modalities](https://arxiv.org/pdf/0809.2494), published 2011; v8 September 2010 | §§9–11: maximality for specified modal, monad/comonad, adjunction and trijunction languages | These are actual maximality results, not merely coherence. Their canonical-arrow languages and universal equations differ from the Boolean theory; no transfer theorem was found. |
| [Symmetric Self-Adjunctions and Matrices](https://arxiv.org/pdf/math/0510039), published 2012; v9 September 2011 | §§7,13: new equations force unequal circle/loop expressions to agree | A nearby reduction method, but the conclusion is not Boolean thinness; compact/self-adjunction structure also differs. |
| [A Faithful 2-Dimensional TQFT](https://arxiv.org/pdf/1711.06044), published 2020; v4 August 2019 | Proposition 2.4, p.4, called MAXIMALITY | Equal images of distinct cobordisms, for \(\dim A>1\), force equality between different closed-surface unions. This reduces to scalar invariants; it does not classify Boolean congruences. |
| [Coherence for closed categories with biproducts](https://arxiv.org/pdf/2001.09736), published 2021; v4 March 2022 | Theorems 7.5,8.3–8.4, pp.13–15 | Faithful graphical interpretations for closed/compact categories with biproducts. Different signature and result. |
| [Coherence for logicians](https://arxiv.org/html/2402.01285v2), Petrić–Zekić, v1 February 2024; v2 July 2026 | Theorem 5.9, p.17, and Proposition 6.5, p.24, in v2 | Kelly–Mac Lane coherence in logical notation: balanced terms of proper type, and a linking criterion for proper types. It does not address extension by arbitrary new equations or Boolean maximality. |

For *Coherence for logicians*, both versions were checked. The July 2026 version formalizes and expands the link-based application; the main coherence result has the same scope. A separate 2026 journal publication was not verified and is not assumed here.

Two titles sometimes described as “later” are earlier preprints: [Coherence and Confluence](https://arxiv.org/pdf/math/0506310) and [Relevant Categories and Partial Functions](https://arxiv.org/pdf/math/0504133) were posted in 2005 and published in 2007. The former discusses coherence and alternative Boolean axiomatizations; the latter treats relevant closed categories, smash product, and partial functions. Neither supplies the target maximality theorem or a counterexample in its exact signature.

Two further 2007 boundary works were checked. [Medial Commutativity](https://arxiv.org/pdf/math/0610934), §5, proves permutation coherence for a single tensor with medial isomorphisms; it states no Boolean maximality theorem. [Proof-Net Categories](https://www.mi.sanu.ac.rs/novi_sajt/biography/kosta/pn.pdf), §4.3, author-preprint p.83, proves a full-subcategory/conservativeness result for multiplicative linear structure. It neither supplies product projections nor asserts conservativity after adjoining arbitrary equations. Under the same object assignment, the Boolean projection \(p\wedge p\to p\) has no proof-net counterpart: a Brauer pairing cannot pair its three occurrences. The book check used the author-designated updated 2005 preprint of the 2007 volume and its [printed-edition corrigenda](https://www.mi.sanu.ac.rs/novi_sajt/biography/kosta/addenda.pdf), not an independently obtained printed volume.

## 7. Why other maximality theorems do not transfer automatically

### 7.1 Zero-lattice, zero-mix, and relational presentations

The familiar selector proof in a category with unrestricted zero arrows can use arrows of types \(p\to A\) and \(C\to p\). In \(\mathsf B\), such types may be uninhabited. For example \(p\to p\wedge\bot\) does not exist. Sending all variables to one variable does not remove the constants. This is exactly why the Boolean isolation ends at \(p\wedge\bot\to p\vee\top\).

Likewise, \(G:\mathsf B\to\mathrm{Rel}_{\mathrm{fin}}\) is not full: there is an empty relation \(G\top\to G\bot\), but no Boolean arrow \(\top\to\bot\). An ambient congruence-collapse result cannot be pulled back merely because \(G\) was faithful before adjoining the new equation. One needs a conservativity result for the enlarged theory, or an explicit lift of the required contexts. Section 4 supplies an effective direct argument instead.

### 7.2 Cartesian and typed Böhm results

Došen–Petrić’s [Maximality of Cartesian Categories](https://arxiv.org/pdf/math/9911059), §5, and [Maximality of the Typed Lambda Calculus and of Cartesian Closed Categories](https://arxiv.org/pdf/math/9911073), §§10–11, are methodological antecedents: substitution and separating contexts force projection equality. The CCC paper itself stresses that its maximality does not automatically imply the cartesian result.

Their [Typed Böhm Theorem](https://www.mi.sanu.ac.rs/~zpetric/krit.pdf), Theorems 6.1–6.2 and corollary, concerns the pure functional calculus. Simpson’s [Categorical Completeness Results for the Simply-typed Lambda-calculus](https://www.pure.ed.ac.uk/ws/files/12417852/download.pdf), Theorems 1 and 3, gives the related completeness/typical-ambiguity results and explains why the argument does not extend indiscriminately to added typed constants. Treating the Boolean structural operations as new CCC constants is therefore not a justified reduction. The faithful-embedding obstruction in §3.2 is stronger still.

## 8. External classical-proof literature and forward checks

| Primary source | Closest issue inspected | Assessment |
|---|---|---|
| Lamarche–Straßburger, [Constructing free Boolean categories](https://www.lix.polytechnique.fr/~lutz/papers/FreeBool.pdf), LICS 2005 | §2.4.6 cloneable-quasientropy subcategory; Theorem 2.4.7 idempotency; Theorem 3.5.4 freeness | The product/coproduct subcategory is a real possible bridge, but no identification with the free zero-identity DP theory or maximality theorem is supplied. The final LICS version was used. |
| Führmann–Pym, [Order-enriched categorical models of the classical sequent calculus](https://doi.org/10.1016/j.jpaa.2005.03.016), 2006 | Equation (11), journal p.28; Theorems 6.4–6.5 | Its negation triangle equals the identity. The corresponding composite in the target theory is a zero identity. Ordered soundness/completeness is not congruence maximality. |
| Straßburger, [On the Axiomatisation of Boolean Categories with and without Medial](https://arxiv.org/pdf/cs/0512086), 2007 | Theorem 8.6 and Corollary 8.7; subsequent net models | The relevant collapse is idempotency of addition, not equality of all parallel arrows. The paper explicitly distinguishes its axioms from DP’s. |
| Lamarche, [Exploring the gap between linear and classical logic](https://www.tac.mta.ca/tac/volumes/18/17/18-17.pdf), 2007 | Introduction and its closure footnote; medial and *-autonomous structure | Explicitly separates the nonclosed DP approach. No target maximality result found. Complete paper inspected through a PDF mirror after the journal endpoint failed. |
| Bellin–Hyland–Robinson–Urban, [Categorical Proof Theory of Classical Propositional Calculus](https://www.dpmms.cam.ac.uk/~jmeh1/Research/Publications/2006/bhru06.pdf), accepted preprint 2006 | Theorems 4.2–4.4: representability and a quotient construction | The source is a guarded/polycategorical model; its quotient retains different identity triangles. This is not a quotient theorem about \(\mathsf B\). |
| Hughes, [Logic Without Syntax](https://arxiv.org/pdf/math/0504065), 2005 | Theorems 1–2 and Boolean constructions in §5 | Representations and proof systems, not the target classification of equational extensions. |
| Cockett–Santocanale, [On the word problem for sigma-pi categories](https://arxiv.org/pdf/0904.1529), 2009 | Freeness through softness; equality algorithm | Bicartesian syntax without the target distributor and negation. No Boolean maximality transfer. |
| Heijltjes–Hughes, [Complexity Bounds for Sum-Product Logic via Additive Proof Nets and Petri Nets](https://purehost.bath.ac.uk/ws/files/119064132/ALL.pdf), 2015 | Introductory “maximality” reference and correctness theorem | “Maximality” there refers to Hu’s maximal maps, not maximal equational theories. |
| Tranchini, [Identity of Proofs](https://link.springer.com/content/pdf/10.1007/978-3-031-46921-3_2.pdf), 2024 | §2.4, printed p.31 | The maximality discussion concerns intuitionistic \(\beta\eta\) equivalence and typed Böhm results. |
| Yamamoto, [Bicategorical models of classical propositional logic](https://arxiv.org/pdf/2308.01662), 2023 | Reductions as 2-cells; extension of FP models | Changes the semantic level; no target equational theorem. |
| Pym–Ritter–Robinson, [Categorical Proof-theoretic Semantics](https://arxiv.org/pdf/2302.09031), revised 2024 | Base-extension semantics | Addresses intuitionistic proof-theoretic semantics, not this maximality conjecture. |
| Acclavio–Straßburger–Zamdzhiev, [Proof Identity and Categorical Models of BV](https://arxiv.org/pdf/2604.25501), 2026 | MLL plus noncommutative seq; categorical soundness | No full product/coproduct Boolean congruence theorem. This was a checked recent endpoint. |

Additional checks included Straßburger’s 2019 survey on proof identity and Hilbert’s 24th problem, which again distinguishes the nonclosed DP route; Lamarche–Novaković’s [2011 TACL slides](https://pageperso.lis-lab.fr/~luigi.santocanale/tacl2011/slides/64.pdf), whose “thin Frobenius” condition is a scalar/loop condition; and Kudzman-Blais’s [CT2025 Linearly Distributive Fox Theorem abstract](https://conference.math.muni.cz/ct2025/data/uploads/abstracts/kudzman-blais.pdf), which states no target collapse theorem.

## 9. Manuscript positioning and revision

The v5 introduction credits cartesian, bicartesian, isomorphism, and split-preorder work. The revision requires precise attribution and a direct statement of the conclusion. Derivability from prior results and prior publication of the result are different claims. The former was established here for contextual collapse; the latter was not established for the maximality theorem.

1. Identify \(h_A\) explicitly as \(\nabla_A m_{A,A}\), citing (dm) and mix symmetry. Retain its short relational verification if useful for self-containment.
2. Cite the p.294 isomorphisms and the proof of Lemma 7 in the 2012 paper. The latter is more consequential than the currently cited occurrence-selection Lemma 6 alone.
3. Consider replacing the longer contextual-collapse calculation with §4.2, or include that calculation as a short alternative proof. The explicit inverses in §4.3 remove any ambiguity about which isomorphisms are intended.
4. State the positive zero-identity result as a consequence if the manuscript’s scope permits. The collapse does not need negation; negation enters the reduction of arbitrary Boolean arrows to signed occurrences.
5. Keep the historical claim exact: the result contradicts the conjecture in the specified September 2007 version. Do not claim that every later author reaffirmed the conjecture, that no one else could have observed the consequence, or that a broadly new maximality method is introduced.

Suggested positioning paragraph:

> We prove maximality of the free zero-identity Boolean category of Došen and Petrić, contrary to their conjecture. The proof combines their contextual reduction with structural isomorphisms already available in the theory. These isomorphisms show that the contextual equation forces equality of the product projections. The contribution is this consequence of the existing coherence and structural results, together with its application to arbitrary Boolean arrow equations.

If the present proof is retained, add:

> The symmetric arrow used below is the mix map followed by the codiagonal. Its parameter independence and symmetry are established mix identities; we give their occurrence interpretation to fix the notation.

The initial novelty review did not change the manuscript. The subsequent authorized v6 revision adopts the structural-isomorphism proof, adds the concrete Joyal comparison, and describes the conditional Lean formalization. It retains the maximality theorem and its stated contradiction of the September 2007 conjecture. The positive zero-identity extension in recommendation 4 is not added as a separate theorem.

### 9.1 Formalization contribution and its present scope

The checked Lean source is revision `1e967bcb913a74ae590dde940f246acaddce1fba`; the v5 manuscript-only successor did not alter it. `DosenPetric/Substitution.lean`, theorem `relative_maximality`, proves totality from a new substitution-closed equation with explicit structural, faithful-interpretation, normalization, signed-label, substitution, and double-negation inputs. `OccurrenceInterpretation.faithful` in `Structure.lean` is a field of that input, not a proved instance for the actual equation-generated presentation.

The development constructs the typed syntax, generated equality, quotient category, structural operations, zero construction, substitution, normalization, and a well-defined signed occurrence interpretation for the source presentation. It also contains substantial progress toward coherence. Faithfulness for that presentation, full general Reducibility, cut elimination, and the unconditional intended instance of maximality remain open. The formal collapse proof uses the symmetric fold; v6’s shorter q/e proof has not been newly formalized. No Lean source changes or fresh full Lean build were part of this manuscript revision.

The formal development is a separate contribution with these precise boundaries. The evidence does not justify declaring it more substantial than the mathematical theorem. A completed kernel-checked proof for the actual presentation would be a further result.

### 9.2 Confidence

Confidence is high in the typed structural-isomorphism derivation and in the stated boundary of the checked Lean theorem. Whether an unlocated earlier publication states the same maximality theorem remains unknown. The broad search below supports a bounded negative finding, not a proof of priority.

## 10. Search coverage and limits

The search combined exact conjecture phrases; accented and ASCII author names; Boolean category/categories with maximality, nonmaximality, Post-completeness, zero-identity, and congruence; the official publication/CV lists; arXiv version histories; and backward/forward examination of the classical-proof-category literature. Promising results were tested by comparing hypotheses, signatures, and conclusions, and by attempting an actual typed derivation.

Petrić’s [official publication page](https://www.mi.sanu.ac.rs/~zpetric/publications.htm) directs readers to his [CV](https://www.mi.sanu.ac.rs/~zpetric/cv.pdf). Every post-2007 paper/manuscript listed there was screened from a primary full text. The later-paper corpus contained 40 distinct works: eight principal works in the §6 table, two 2007 boundary papers (*Coherence and Confluence* and *Relevant Categories and Partial Functions*), and 30 appendix entries. A second version of *Coherence for logicians* and the CV brought that collection to 42 PDFs. The separate *Medial Commutativity* and *Proof-Net Categories* checks are additional. Screening unrelated papers meant checking scope, theorem statements, conclusions, and relevant terms—not certifying every proof in those papers. Priority sources received detailed reading; the contextual-collapse implication was checked independently.

This is a broad, documented novelty audit, not a proof that no prior statement exists. A complete export of every forward citation was unavailable; publisher versions were not systematically diffed against all author versions. Szabo’s 1974 *A categorical characterization of Boolean algebras* was identified through its [publisher record](https://doi.org/10.1007/BF02485724) and primary references, but its full text was unavailable. Lambek–Scott was inspected through a full-text OCR mirror and corroborated by the primary sources above. The inaccessible short paper associated with the 2011 Lamarche–Novaković slides was not treated as fully examined.

Two external full-text gaps remained after retries through author, repository, publisher, and mirror endpoints: Straßburger’s [What Is the Problem with Proof Nets for Classical Logic?](https://link.springer.com/chapter/10.1007/978-3-642-13962-8_45) (2010), and [From Deep Inference to Proof Nets via Cut Elimination](https://doi.org/10.1093/logcom/exp047) (online 2009, issue 2011). The first paper’s indexed opening passage invokes cartesian closure, but neither paper was counted as fully examined. These access limits affect the negative literature claim, not the explicit derivation in §4.

The positive findings—old mix structure and the short isomorphism proof—are firmer than the negative finding that no earlier explicit theorem was located.

## Appendix: later-Petrić coverage ledger

The principal works are discussed in §6. The following remaining works were screened from full text; the last column records why they do not state the target theorem. A category-theoretic title or the word “maximality” alone was not taken as evidence of subsumption.

| Work | Primary text | Relevant scope |
|---|---|---|
| Equality of Proofs for Linear Equality (2008) | [math/0601490](https://arxiv.org/pdf/math/0601490) | Equality predicate and multiplicative conjunction; coherence. |
| Coherence in Linear Predicate Logic (2009) | [0709.1421](https://arxiv.org/pdf/0709.1421) | First-order linear fragments and proof-net coherence. |
| Coherence for Monoidal Endofunctors (2010) | [0907.2194](https://arxiv.org/pdf/0907.2194) | Monoidal endofunctor coherence. |
| Coherence for Monoidal Monads and Comonads (2010) | [0907.2199](https://arxiv.org/pdf/0907.2199) | Graphical coherence for specified monad/comonad structures. |
| Hypergraph Polytopes (2011) | [1010.5477](https://arxiv.org/pdf/1010.5477) | Hypergraph/polytope constructions. |
| Intermutation (2012; revised 2013) | [math/0701325](https://arxiv.org/pdf/math/0701325) | Restricted coherence for intermutation; no target maximality. |
| Shuffles and Concatenations in Constructing of Graphs (2012) | [1002.3577](https://arxiv.org/pdf/1002.3577) | Graph-construction presentations. |
| Graphs for Juncture (2012 preprint) | [Author PDF](https://www.mi.sanu.ac.rs/novi_sajt/biography/kosta/jun.pdf) | Alternative 2-category composition and completeness of graph syntax. |
| Ordinals in Frobenius Monads (2013) | [0809.2495](https://arxiv.org/pdf/0809.2495) | Frobenius monads and ordinal-labelled normal forms. |
| Graphs of Plural Cuts (2013) | [1104.4064](https://arxiv.org/pdf/1104.4064) | Graphs for plural cuts and composition. |
| On Stretching the Interval Simplex-Permutohedron (2014) | [1106.3250](https://arxiv.org/pdf/1106.3250) | Nested sets and polytope subdivision. |
| Symmetric Bimonoidal Intermuting Categories and ω×ω Reduced Bar Constructions (2014) | [0906.2954](https://arxiv.org/pdf/0906.2954) | Restricted coherence and reduced bar constructions. |
| Classifying Spaces of Monoidal Categories (2014, Serbian) | [Author PDF](https://www.mi.sanu.ac.rs/~zpetric/raspetljavanje.pdf) | Segal–Thomason/classifying-space constructions. |
| Segal’s Multisimplicial Spaces (2015) | [1407.3914](https://arxiv.org/pdf/1407.3914) | Deloopings and multisimplicial conditions. |
| Weak Cat-Operads (2015) | [1005.4633](https://arxiv.org/pdf/1005.4633) | Equational coherence for categorified operad insertions. |
| Monoids, Segal’s Condition and Bisimplicial Spaces (2015) | [1505.05010](https://arxiv.org/pdf/1505.05010) | Topological monoids and nerves. |
| A Planarity Criterion for Graphs (2015) | [1203.0996](https://arxiv.org/pdf/1203.0996) | Graph planarity via grounded cocycles. |
| 270 Minutes on Categorial Proof Theory (2015) | [Author PDF](https://www.mi.sanu.ac.rs/~zpetric/270min.pdf) | Introductory implicational/conjunctive systems and cartesian coherence. |
| Representing Conjunctive Deductions by Disjunctive Deductions (2017) | [1511.05462](https://arxiv.org/pdf/1511.05462) | Representations of free product/coproduct categories. |
| A Note on Semisymmetry (2017) | [1507.02149](https://arxiv.org/pdf/1507.02149) | Quasigroups and semisymmetrization. |
| The n-Fold Reduced Bar Construction (2018) | [1309.6209](https://arxiv.org/pdf/1309.6209) | Lax functors and delooping constructions. |
| Spheres as Frobenius Objects (2018) | [1609.03979](https://arxiv.org/pdf/1609.03979) | Frobenius syntax and sphere-cobordism faithfulness. |
| A Simple Permutoassociahedron (2019) | [1708.02482](https://arxiv.org/pdf/1708.02482) | Polytope realization; maximal faces, not maximal theories. |
| Proofs and Surfaces (2020) | [1907.02949](https://arxiv.org/pdf/1907.02949) | Menelaus configurations, geometry, and sequent systems. |
| A Diagrammatic Calculus for Categorical Quantum Protocols (2024) | [2206.03294](https://arxiv.org/pdf/2206.03294) | Compact closure, biproducts, and labelled-cobordism matrices. |
| A Diagrammatic Presentation of the Category 3Cob (2024) | [2302.06428](https://arxiv.org/pdf/2302.06428) | Presentation of three-dimensional cobordisms. |
| Chromatic Numbers for Facet Colouring of Some Generalized Associahedra (2024) | [2311.05901](https://arxiv.org/pdf/2311.05901) | Polytope facet colouring. |
| From Heegaard Diagrams to Surgery (2025) | [2308.01908](https://arxiv.org/pdf/2308.01908) | Heegaard-to-framed-link procedure. |
| A Calculus for S3-Diagrams of Manifolds with Boundary (manuscript) | [2111.11311](https://arxiv.org/pdf/2111.11311) | Completeness of diagram moves for manifolds. |
| Restricted (2+1)-TQFTs Supported by Thickened and Solid Tori (2025 manuscript) | [2505.21373](https://arxiv.org/pdf/2505.21373) | Restricted cobordism categories and TQFT distinctions. |
