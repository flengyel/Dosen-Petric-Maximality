module

public import DosenPetric.Isolation

@[expose] public section

set_option autoImplicit false

namespace DosenPetric

universe u v

/-- Substitution acts on arrows and both endpoint formulas, preserving the fragment operations. -/
structure Substitution {P : Type u} {C : Category.{u,v} (Formula P)}
    (S : Structure C) (Z : ZeroIdentity C) where
  map : (σ : P → Formula P) → {A B : Formula P} → C.Hom A B → C.Hom (A.subst σ) (B.subst σ)
  map_id : ∀ σ A, map σ (C.id A) = C.id (A.subst σ)
  map_comp : ∀ σ {A B D} (f : C.Hom A B) (g : C.Hom B D),
    map σ (C.comp f g) = C.comp (map σ f) (map σ g)
  map_fst : ∀ σ A B, map σ (S.fst A B) = S.fst (A.subst σ) (B.subst σ)
  map_snd : ∀ σ A B, map σ (S.snd A B) = S.snd (A.subst σ) (B.subst σ)
  map_pair : ∀ σ {X A B} (f : C.Hom X A) (g : C.Hom X B),
    map σ (S.pair f g) = S.pair (map σ f) (map σ g)
  map_inl : ∀ σ A B, map σ (S.inl A B) = S.inl (A.subst σ) (B.subst σ)
  map_inr : ∀ σ A B, map σ (S.inr A B) = S.inr (A.subst σ) (B.subst σ)
  map_copair : ∀ σ {A B X} (f : C.Hom A X) (g : C.Hom B X),
    map σ (S.copair f g) = S.copair (map σ f) (map σ g)
  map_toTop : ∀ σ A, map σ (S.toTop A) = S.toTop (A.subst σ)
  map_fromBot : ∀ σ A, map σ (S.fromBot A) = S.fromBot (A.subst σ)
  map_dist : ∀ σ A B D, map σ (S.dist A B D) = S.dist (A.subst σ) (B.subst σ) (D.subst σ)
  map_zero : ∀ σ A, map σ (Z.zero A) = Z.zero (A.subst σ)

/-- The double-negation comparison is given by arrows and their inverse equations. -/
structure DoubleNegation {P : Type u} (C : Category.{u,v} (Formula P)) where
  into : (A : Formula P) → C.Hom A (.neg (.neg A))
  out : (A : Formula P) → C.Hom (.neg (.neg A)) A
  into_out : ∀ A, C.comp (into A) (out A) = C.id A
  out_into : ∀ A, C.comp (out A) (into A) = C.id (.neg (.neg A))

namespace Substitution

variable {P : Type u} {C : Category.{u,v} (Formula P)} {S : Structure C}
  {Z : ZeroIdentity C} (U : Substitution S Z)

def Closed (Q : Congruence S) : Prop :=
  ∀ σ {A B : Formula P} {f g : C.Hom A B}, Q.Rel f g → Q.Rel (U.map σ f) (U.map σ g)

theorem map_zeroOf (σ : P → Formula P) {A B : Formula P} (f : C.Hom A B) :
    U.map σ (Z.zeroOf f) = Z.zeroOf (U.map σ f) := by
  rw [ZeroIdentity.zeroOf, U.map_comp, U.map_zero]
  rfl

theorem map_context (σ : P → Formula P) (A : Formula P) :
    U.map σ (C.comp (S.fst A .bot) (S.j A)) =
      C.comp (S.fst (A.subst σ) .bot) (S.j (A.subst σ)) := by
  rw [U.map_comp, U.map_fst, Structure.j, U.map_inl]
  rfl

theorem context_subst (Q : Congruence S) (closed : U.Closed Q) (σ : P → Formula P)
    (A : Formula P) (h : ContextualCollapse.K Q (Z := Z) A) :
    ContextualCollapse.K Q (Z := Z) (A.subst σ) := by
  have hh := closed σ h
  rw [U.map_zeroOf, U.map_context] at hh
  exact hh

end Substitution

namespace ContextualCollapse

variable {P : Type u} {C : Category.{u,v} (Formula P)} {S : Structure C}
  {Z : ZeroIdentity C} (Q : Congruence S)

/-- A contextual equation transports along a retract by product and coproduct maps. -/
theorem context_retract {A B : Formula P} (m : C.Hom A B) (n : C.Hom B A)
    (hmn : C.comp m n = C.id A) (h : K Q (Z := Z) B) : K Q (Z := Z) A := by
  let pre := S.prodMap m (C.id .bot)
  let post := S.sumMap n (C.id .top)
  have e : C.comp (C.comp pre (C.comp (S.fst B .bot) (S.j B))) post =
      C.comp (S.fst A .bot) (S.j A) := by
    dsimp only [pre, post, Structure.prodMap, Structure.sumMap, Structure.j]
    rw [← C.assoc _ (S.fst B .bot), S.pair_fst, C.assoc, C.assoc,
      S.inl_copair, ← C.assoc m n, hmn, C.id_comp]
  have hz : C.comp (C.comp pre (Z.zeroOf (C.comp (S.fst B .bot) (S.j B)))) post =
      Z.zeroOf (C.comp (S.fst A .bot) (S.j A)) := by
    rw [Z.precompose, Z.postcompose, e]
  have hh := Q.post (Q.pre pre h) post
  rw [e, hz] at hh
  exact hh

theorem all_contexts (U : Substitution S Z) (D : DoubleNegation C) (closed : U.Closed Q)
    (l : Literal P) (h : K Q (Z := Z) l.formula) : ∀ A, K Q (Z := Z) A := by
  intro A
  cases l with
  | pos p => exact U.context_subst Q closed (fun _ => A) (.var p) h
  | neg p =>
    have hn := U.context_subst Q closed (fun _ => .neg A) (.neg (.var p)) h
    exact context_retract Q (D.into A) (D.out A) (D.into_out A) hn

end ContextualCollapse

/-- Relative maximality under explicit structural, coherence, normalization,
signed-label, and arrow-substitution data. No free-presentation bridge is inferred. -/
theorem relative_maximality {P : Type u} {C : Category.{u,v} (Formula P)}
    {S : Structure C} {Z : ZeroIdentity C} (I : OccurrenceInterpretation S Z)
    (N : Normalization C) (labels : SignedLabelPreservation I)
    (U : Substitution S Z) (D : DoubleNegation C) (Q : Congruence S) (closed : U.Closed Q)
    {A B : Formula P} (f g : C.Hom A B) (hne : f ≠ g) (hfg : Q.Rel f g) : Q.Total := by
  obtain ⟨l, hl⟩ := Isolation.normalized_literal_context I N labels Q f g hne hfg
  exact ContextualCollapse.total I Q (ContextualCollapse.all_contexts Q U D closed l hl)

end DosenPetric
