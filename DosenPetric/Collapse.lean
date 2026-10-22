module

public import DosenPetric.OccurrenceLaws

@[expose] public section

set_option autoImplicit false

namespace DosenPetric.ContextualCollapse

universe u v

variable {P : Type u} {C : Category.{u,v} (Formula P)} {S : Structure C}
  {Z : ZeroIdentity C} (I : OccurrenceInterpretation S Z) (Q : Congruence S)

/-- The contextual equation K_A, with its zero defined from an existing arrow. -/
def K (A : Formula P) : Prop :=
  Q.Rel (C.comp (S.fst A .bot) (S.j A))
    (Z.zeroOf (C.comp (S.fst A .bot) (S.j A)))

variable (allK : ∀ A, K Q (Z := Z) A)

include I allK

theorem second_block (A : Formula P) :
    Q.Rel (C.comp (S.fold A .bot) (S.j A)) (C.comp (S.snd A A) (S.j A)) := by
  rw [Structure.fold, C.assoc, S.copair_comp, C.id_comp]
  have h := Q.pre (S.u A .bot) (Q.copair (allK A) (Q.refl (S.j A)))
  rw [I.second_block] at h
  exact h

theorem injected_projections (A : Formula P) :
    Q.Rel (C.comp (S.fst A A) (S.j A)) (C.comp (S.snd A A) (S.j A)) := by
  have h := second_block I Q allK A
  have hs := Q.pre (S.swap A) h
  rw [← C.assoc, I.fold_swap, ← C.assoc, Structure.swap, S.pair_snd] at hs
  exact Q.trans (Q.symm hs) h

theorem terminal_injection (A : Formula P) :
    Q.Rel (S.j A) (C.comp (S.toTop A) (S.inr A .top)) := by
  have h := Q.pre (S.pair (C.id A) (Z.zero A)) (injected_projections I Q allK A)
  rw [← C.assoc, ← C.assoc, S.pair_fst, S.pair_snd, C.id_comp] at h
  change Q.Rel (S.j A) (Z.zeroOf (S.j A)) at h
  rw [← I.through_top (S.toTop A) (S.inr A .top) (S.j A)] at h
  exact h

/-- The retraction of the terminal summand is inverse modulo the congruence. -/
theorem terminal_retraction (A : Formula P) :
    Q.Rel (C.comp (S.toTop (.disj A .top)) (S.inr A .top)) (C.id (.disj A .top)) := by
  apply Q.copair_ext
  · rw [← C.assoc, S.toTop_unique (C.comp (S.inl A .top) (S.toTop (.disj A .top))),
      C.comp_id]
    exact Q.symm (terminal_injection I Q allK A)
  · rw [← C.assoc,
      S.toTop_unique (C.comp (S.inr A .top) (S.toTop (.disj A .top))),
      ← S.toTop_unique (C.id .top), C.id_comp, C.comp_id]
    exact Q.refl _

/-- Terminality is uniqueness of existing arrows together with a specified arrow. -/
theorem terminal_hom (A X : Formula P) (f : C.Hom X (.disj A .top)) :
    Q.Rel f (C.comp (S.toTop X) (S.inr A .top)) := by
  have h := Q.pre f (terminal_retraction I Q allK A)
  rw [C.comp_id, ← C.assoc,
    S.toTop_unique (C.comp f (S.toTop (.disj A .top)))] at h
  exact Q.symm h

/-- Copairing exchanges the summands of A ∨ top. -/
theorem other_injection (A : Formula P) :
    Q.Rel (S.inr .top A) (C.comp (S.toTop A) (S.inl .top A)) := by
  have h := Q.post (terminal_injection I Q allK A)
    (S.copair (S.inr .top A) (S.inl .top A))
  rw [Structure.j, S.inl_copair, C.assoc, S.inr_copair] at h
  exact h

theorem fold_top (A : Formula P) : Q.Rel (S.fold A .top) (S.fst A A) := by
  have hi := Q.prodMap (Q.refl (C.id A)) (other_injection I Q allK A)
  have h := Q.post (Q.post hi (S.dist A .top A))
    (S.copair (S.fst A .top) (C.id A))
  change Q.Rel (S.fold A .top) _ at h
  have e :
      C.comp
        (C.comp (S.prodMap (C.id A) (C.comp (S.toTop A) (S.inl .top A)))
          (S.dist A .top A))
        (S.copair (S.fst A .top) (C.id A)) = S.fst A A := by
    have pm : S.prodMap (C.id A) (C.comp (S.toTop A) (S.inl .top A)) =
        C.comp (S.prodMap (C.id A) (S.toTop A)) (S.prodMap (C.id A) (S.inl .top A)) := by
      rw [S.prodMap_comp, C.id_comp]
    rw [pm, C.assoc (S.prodMap (C.id A) (S.toTop A))
      (S.prodMap (C.id A) (S.inl .top A)) (S.dist A .top A),
      I.first_injection, C.assoc, S.inl_copair]
    unfold Structure.prodMap
    rw [S.pair_fst, C.comp_id]
  exact e ▸ h

theorem equal_projections (A : Formula P) : Q.Rel (S.fst A A) (S.snd A A) := by
  have h := fold_top I Q allK A
  have hs := Q.pre (S.swap A) h
  rw [I.fold_swap, Structure.swap, S.pair_fst] at hs
  exact Q.trans (Q.symm h) hs

/-- If K_A holds for every formula, the congruence identifies every parallel pair. -/
theorem total : Q.Total := by
  intro X A f g
  have h := Q.pre (S.pair f g) (equal_projections I Q allK A)
  rw [S.pair_fst, S.pair_snd] at h
  exact h

end DosenPetric.ContextualCollapse
