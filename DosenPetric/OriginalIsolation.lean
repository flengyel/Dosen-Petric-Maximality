module

public import DosenPetric.PresentationShortMaximality

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Isolation
universe u v
variable {P : Type u} {C : Category.{u,v} (Formula P)}
  {S : Structure C} {Z : ZeroIdentity C}

/-- Reattach a normalized selector and coselector to the original endpoints. -/
theorem original_composite (N : Normalization C) {A B : Formula P}
    {X Y : Formula P} (i : C.Hom X (N.normal A).formula)
    (r : C.Hom (N.normal B).formula Y) (f : C.Hom A B) :
    C.comp (C.comp (C.comp i (N.backward A)) f) (C.comp (N.forward B) r) =
      C.comp (C.comp i (N.transport f)) r := by
  simp only [Normalization.transport,C.assoc]

/-- The exact original-endpoint occurrence-isolation statement, allowing the
specified interchange of the two arrows. -/
theorem original_witnesses (I : OccurrenceInterpretation S Z) (N : Normalization C)
    (labels : SignedLabelPreservation I) {A B : Formula P} (f g : C.Hom A B) (hne : f ≠ g) :
    ∃ (l : Literal P) (i : C.Hom (.conj l.formula .bot) A)
      (r : C.Hom B (.disj l.formula .top)),
      (C.comp (C.comp i f) r = C.comp (S.fst l.formula .bot) (S.j l.formula) ∧
       C.comp (C.comp i g) r = Z.zeroOf (C.comp (S.fst l.formula .bot) (S.j l.formula))) ∨
      (C.comp (C.comp i g) r = C.comp (S.fst l.formula .bot) (S.j l.formula) ∧
       C.comp (C.comp i f) r = Z.zeroOf (C.comp (S.fst l.formula .bot) (S.j l.formula))) := by
  have hr : I.map (N.transport f) ≠ I.map (N.transport g) := by
    intro h
    exact hne (N.transport_injective (I.faithful h))
  have oriented (a b : C.Hom A B)
      (he : ∃ x y, I.map (N.transport a) x y ∧ ¬ I.map (N.transport b) x y) :
      ∃ (l : Literal P) (i : C.Hom (.conj l.formula .bot) A)
        (r : C.Hom B (.disj l.formula .top)),
        C.comp (C.comp i a) r = C.comp (S.fst l.formula .bot) (S.j l.formula) ∧
        C.comp (C.comp i b) r = Z.zeroOf (C.comp (S.fst l.formula .bot) (S.j l.formula)) := by
    obtain ⟨x,y,ha,hb⟩ := he
    obtain ⟨i,r,hi,hr⟩ := isolate_edge I (N.normal A) (N.normal B) (N.transport a) (N.transport b)
      x y (labels _ _ _ x y ha) ha hb
    refine ⟨(N.normal A).literalAt x,C.comp i (N.backward A),C.comp (N.forward B) r,?_,?_⟩
    · rw [original_composite]
      exact hi
    · rw [original_composite]
      exact hr
  rcases differing_edge hr with he | he
  · obtain ⟨l,i,r,hi,hr⟩ := oriented f g he
    exact ⟨l,i,r,Or.inl ⟨hi,hr⟩⟩
  · obtain ⟨l,i,r,hi,hr⟩ := oriented g f he
    exact ⟨l,i,r,Or.inr ⟨hi,hr⟩⟩

end DosenPetric.Isolation
namespace DosenPetric.Presentation
universe u
variable {P : Type u}

/-- Manuscript Lemma 4.1 in the actual equation-generated category. -/
theorem occurrence_isolation {A B : Formula P} (f g : Hom A B) (hne : f ≠ g) :
    ∃ (l : Literal P) (i : Hom (.conj l.formula .bot) A) (r : Hom B (.disj l.formula .top)),
      (comp (comp i f) r = comp (fst l.formula .bot) (inl l.formula .top) ∧
       comp (comp i g) r = (zeroIdentity P).zeroOf (comp (fst l.formula .bot) (inl l.formula .top))) ∨
      (comp (comp i g) r = comp (fst l.formula .bot) (inl l.formula .top) ∧
       comp (comp i f) r = (zeroIdentity P).zeroOf (comp (fst l.formula .bot) (inl l.formula .top))) :=
  Isolation.original_witnesses (interpretation P) (normalization P) (interpretation_signedLabel P) f g hne

end DosenPetric.Presentation
