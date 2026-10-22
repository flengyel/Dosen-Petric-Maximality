module

public import DosenPetric.NormalForm

@[expose] public section

set_option autoImplicit false

namespace DosenPetric.Isolation

universe u v

variable {P : Type u} {C : Category.{u,v} (Formula P)} (S : Structure C)

def blank (l : Literal P) (A : Formula P) : C.Hom (Formula.conj l.formula .bot) A :=
  C.comp (S.snd l.formula .bot) (S.fromBot A)

def discard (l : Literal P) (A : Formula P) : C.Hom A (Formula.disj l.formula .top) :=
  C.comp (S.toTop A) (S.inr l.formula .top)

def selector : (A : NormalForm P) → (x : A.formula.Occ) →
    C.Hom (Formula.conj (A.literalAt x).formula .bot) A.formula
  | .lit l, _ => S.fst l.formula .bot
  | .top, x => nomatch x
  | .bot, x => nomatch x
  | .conj A B, .inl x => S.pair (selector A x) (blank S (A.literalAt x) B.formula)
  | .conj A B, .inr x => S.pair (blank S (B.literalAt x) A.formula) (selector B x)
  | .disj A B, .inl x => C.comp (selector A x) (S.inl A.formula B.formula)
  | .disj A B, .inr x => C.comp (selector B x) (S.inr A.formula B.formula)

def coselector : (A : NormalForm P) → (x : A.formula.Occ) →
    C.Hom A.formula (Formula.disj (A.literalAt x).formula .top)
  | .lit l, _ => S.j l.formula
  | .top, x => nomatch x
  | .bot, x => nomatch x
  | .conj A B, .inl x => C.comp (S.fst A.formula B.formula) (coselector A x)
  | .conj A B, .inr x => C.comp (S.snd A.formula B.formula) (coselector B x)
  | .disj A B, .inl x => S.copair (coselector A x) (discard S (A.literalAt x) B.formula)
  | .disj A B, .inr x => S.copair (discard S (B.literalAt x) A.formula) (coselector B x)

variable {S} {Z : ZeroIdentity C} (I : OccurrenceInterpretation S Z)

theorem blank_edge (l : Literal P) (A : Formula P) (d : (Formula.conj l.formula .bot).Occ)
    (y : A.Occ) : ¬ I.map (blank S l A) d y := by
  rw [blank, I.map_comp]
  rintro ⟨e, _, _⟩
  exact Empty.elim e

theorem discard_edge (l : Literal P) (A : Formula P) (x : A.Occ)
    (e : (Formula.disj l.formula .top).Occ) : ¬ I.map (discard S l A) x e := by
  rw [discard, I.map_comp]
  rintro ⟨d, _, _⟩
  exact Empty.elim d

theorem selector_edge (A : NormalForm P) (x : A.formula.Occ)
    (d : (Formula.conj (A.literalAt x).formula .bot).Occ) (y : A.formula.Occ) :
    I.map (selector S A x) d y ↔ y = x := by
  induction A with
  | lit l =>
    change I.map (S.fst l.formula .bot) d y ↔ y = x
    rw [I.map_fst]
    cases d with
    | inl a =>
      change a = y ↔ y = x
      rw [l.occ_unique a, l.occ_unique y, l.occ_unique x]
    | inr e => exact Empty.elim e
  | top => exact Empty.elim x
  | bot => exact Empty.elim x
  | conj A B ha hb =>
    cases x with
    | inl x =>
      change I.map (S.pair (selector S A x) (blank S (A.literalAt x) B.formula)) d y ↔ _
      rw [I.map_pair]
      cases y <;> simp [Relations.pair, ha, blank_edge I]
    | inr x =>
      change I.map (S.pair (blank S (B.literalAt x) A.formula) (selector S B x)) d y ↔ _
      rw [I.map_pair]
      cases y <;> simp [Relations.pair, hb, blank_edge I]
  | disj A B ha hb =>
    cases x with
    | inl x =>
      change I.map (C.comp (selector S A x) (S.inl A.formula B.formula)) d y ↔ _
      rw [I.map_comp, I.map_inl]
      simp [Relations.comp, Relations.graph, ha, eq_comm]
    | inr x =>
      change I.map (C.comp (selector S B x) (S.inr A.formula B.formula)) d y ↔ _
      rw [I.map_comp, I.map_inr]
      simp [Relations.comp, Relations.graph, hb, eq_comm]

theorem coselector_edge (A : NormalForm P) (x : A.formula.Occ) (y : A.formula.Occ)
    (e : (Formula.disj (A.literalAt x).formula .top).Occ) :
    I.map (coselector S A x) y e ↔ y = x := by
  induction A with
  | lit l =>
    change I.map (S.inl l.formula .top) y e ↔ y = x
    rw [I.map_inl]
    cases e with
    | inl a =>
      change Sum.inl y = Sum.inl a ↔ y = x
      rw [l.occ_unique a, l.occ_unique y, l.occ_unique x]
      simp
    | inr e => exact Empty.elim e
  | top => exact Empty.elim x
  | bot => exact Empty.elim x
  | conj A B ha hb =>
    cases x with
    | inl x =>
      change I.map (C.comp (S.fst A.formula B.formula) (coselector S A x)) y e ↔ _
      rw [I.map_comp, I.map_fst]
      cases y <;> simp [Relations.comp, Relations.fstRel, ha]
    | inr x =>
      change I.map (C.comp (S.snd A.formula B.formula) (coselector S B x)) y e ↔ _
      rw [I.map_comp, I.map_snd]
      cases y <;> simp [Relations.comp, Relations.sndRel, hb]
  | disj A B ha hb =>
    cases x with
    | inl x =>
      change I.map (S.copair (coselector S A x) (discard S (A.literalAt x) B.formula)) y e ↔ _
      rw [I.map_copair]
      cases y <;> simp [Relations.copair, ha, discard_edge I]
    | inr x =>
      change I.map (S.copair (discard S (B.literalAt x) A.formula) (coselector S B x)) y e ↔ _
      rw [I.map_copair]
      cases y <;> simp [Relations.copair, hb, discard_edge I]

theorem contextual_edge (l : Literal P) (d : (Formula.conj l.formula .bot).Occ)
    (e : (Formula.disj l.formula .top).Occ) :
    I.map (C.comp (S.fst l.formula .bot) (S.j l.formula)) d e := by
  rw [I.map_comp, I.map_fst, Structure.j, I.map_inl]
  cases d with
  | inr d => exact Empty.elim d
  | inl d =>
    cases e with
    | inr e => exact Empty.elim e
    | inl e =>
      exact ⟨l.point, l.occ_unique d, congrArg Sum.inl (l.occ_unique e).symm⟩

theorem selector_for (A : NormalForm P) (x : A.formula.Occ) (l : Literal P)
    (hl : A.literalAt x = l) :
    ∃ i : C.Hom (.conj l.formula .bot) A.formula,
      ∀ d y, I.map i d y ↔ y = x := by
  subst l
  exact ⟨selector S A x, selector_edge I A x⟩

theorem coselector_for (A : NormalForm P) (x : A.formula.Occ) (l : Literal P)
    (hl : A.literalAt x = l) :
    ∃ r : C.Hom A.formula (.disj l.formula .top),
      ∀ y e, I.map r y e ↔ y = x := by
  subst l
  exact ⟨coselector S A x, coselector_edge I A x⟩

theorem isolate_edge (A B : NormalForm P) (f g : C.Hom A.formula B.formula)
    (x : A.formula.Occ) (y : B.formula.Occ) (hl : A.literalAt x = B.literalAt y)
    (hf : I.map f x y) (hg : ¬ I.map g x y) :
    ∃ (i : C.Hom (.conj (A.literalAt x).formula .bot) A.formula)
      (r : C.Hom B.formula (.disj (A.literalAt x).formula .top)),
      C.comp (C.comp i f) r = C.comp (S.fst (A.literalAt x).formula .bot) (S.j (A.literalAt x).formula) ∧
      C.comp (C.comp i g) r = Z.zeroOf
        (C.comp (S.fst (A.literalAt x).formula .bot) (S.j (A.literalAt x).formula)) := by
  obtain ⟨i, hi⟩ := selector_for I A x (A.literalAt x) rfl
  obtain ⟨r, hr⟩ := coselector_for I B y (A.literalAt x) hl.symm
  have calc_edge (t : C.Hom A.formula B.formula) (d) (e) :
      I.map (C.comp (C.comp i t) r) d e ↔ I.map t x y := by
    rw [I.map_comp, I.map_comp]
    simp [Relations.comp, hi, hr]
  refine ⟨i, r, ?_, ?_⟩
  · apply I.faithful
    funext d e
    apply propext
    exact ⟨fun _ => contextual_edge I _ d e, fun _ => (calc_edge f d e).mpr hf⟩
  · apply I.faithful
    rw [I.map_zeroOf]
    funext d e
    apply propext
    exact ⟨fun h => hg ((calc_edge g d e).mp h), False.elim⟩

theorem differing_edge {X Y : Type} {r s : Relations.Rel X Y} (h : r ≠ s) :
    (∃ x y, r x y ∧ ¬ s x y) ∨ (∃ x y, s x y ∧ ¬ r x y) := by
  classical
  by_cases he : ∃ x y, r x y ∧ ¬ s x y
  · exact Or.inl he
  · apply Or.inr
    apply Classical.byContradiction
    intro hn
    apply h
    funext x y
    apply propext
    constructor
    · intro hr
      apply Classical.byContradiction
      intro hs
      exact he ⟨x, y, hr, hs⟩
    · intro hs
      apply Classical.byContradiction
      intro hr
      exact hn ⟨x, y, hs, hr⟩

include I

/-- An identified distinct normal-form pair yields K for a signed literal. -/
theorem literal_context (labels : SignedLabelPreservation I) (Q : Congruence S)
    (A B : NormalForm P) (f g : C.Hom A.formula B.formula)
    (hne : f ≠ g) (hfg : Q.Rel f g) :
    ∃ l : Literal P, ContextualCollapse.K Q (Z := Z) l.formula := by
  have hrel : I.map f ≠ I.map g := fun h => hne (I.faithful h)
  have oriented {a b : C.Hom A.formula B.formula} (hab : Q.Rel a b)
      (he : ∃ x y, I.map a x y ∧ ¬ I.map b x y) :
      ∃ l : Literal P, ContextualCollapse.K Q (Z := Z) l.formula := by
    obtain ⟨x, y, ha, hb⟩ := he
    obtain ⟨i, r, ei, er⟩ := isolate_edge I A B a b x y (labels A B a x y ha) ha hb
    have h := Q.post (Q.pre i hab) r
    rw [ei, er] at h
    exact ⟨A.literalAt x, h⟩
  rcases differing_edge hrel with he | he
  · exact oriented hfg he
  · exact oriented (Q.symm hfg) he

/-- Normalization uses inverse arrows before coherence is applied. -/
theorem normalized_literal_context (N : Normalization C) (labels : SignedLabelPreservation I)
    (Q : Congruence S) {A B : Formula P} (f g : C.Hom A B)
    (hne : f ≠ g) (hfg : Q.Rel f g) :
    ∃ l : Literal P, ContextualCollapse.K Q (Z := Z) l.formula := by
  exact literal_context I labels Q (N.normal A) (N.normal B) (N.transport f) (N.transport g)
    (fun h => hne (N.transport_injective h)) (Q.post (Q.pre (N.backward A) hfg) (N.forward B))

end DosenPetric.Isolation
