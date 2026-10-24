module

public import DosenPetric.GentzenContractionPrepend
public import DosenPetric.GentzenContractionMixComponents

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace ContractionBlock
variable {F K : List (NormalForm P)} (d : ContractionBlock P F K) (hn : 2 ≤ d.gs.length)
theorem prepend_join (o : Op) (Ξ : List (NormalForm P)) :
    (side P o).comp (join o Ξ K) ((d.prepend hn Ξ).route.sideArrow o) =
      (side P o).comp ((sideM P o).tensor ((side P o).id (fold o Ξ)) (d.route.sideArrow o))
        (join o Ξ F) := by
  let C := side P o
  let D := sideD P o
  apply side_ext o
  intro A a
  cases At.cases_append Ξ F a with
  | inl h =>
    obtain ⟨a,rfl⟩ := h
    rw [C.assoc,Route.sideArrow_get,d.prepend_before,join_before,
      C.assoc,join_before,← C.assoc,← D.fst_nat,C.comp_id]
  | inr h =>
    obtain ⟨a,rfl⟩ := h
    rw [C.assoc,Route.sideArrow_get,d.prepend_shift,join_shift,
      C.assoc,join_shift,← C.assoc,← D.snd_nat,C.assoc,Route.sideArrow_get]
theorem prepend_split (o : Op) (Ξ : List (NormalForm P)) :
    (side P o).comp ((d.prepend hn Ξ).route.sideArrow o) (split o Ξ F) =
      (side P o).comp (split o Ξ K)
        ((sideM P o).tensor ((side P o).id (fold o Ξ)) (d.route.sideArrow o)) := by
  let C := side P o
  apply DiagonalData.cancel_left (C := C) _ _ (join o Ξ K) (split o Ξ K) (split_join o Ξ K)
  rw [← C.assoc,d.prepend_join,C.assoc,join_split,C.comp_id,
    ← C.assoc,join_split,C.id_comp]
theorem prepend_product (Ξ : List (NormalForm P)) :
    comp (ofTerm (d.prepend hn Ξ).route.product) (ofTerm (append .conj Ξ F).invTerm) =
      comp (ofTerm (append .conj Ξ K).invTerm) (tensor .conj (id (ante Ξ)) (ofTerm d.route.product)) :=
  d.prepend_split hn .conj Ξ
theorem prepend_coproduct (Ξ : List (NormalForm P)) :
    comp (ofTerm (append .disj Ξ F).toTerm) (ofTerm (d.prepend hn Ξ).route.coproduct) =
      comp (tensor .disj (id (succ Ξ)) (ofTerm d.route.coproduct)) (ofTerm (append .disj Ξ K).toTerm) :=
  d.prepend_split hn .disj Ξ
theorem otherMixL {Φ Ψ Δ : List (NormalForm P)}
    (g : Term P (ante F) (succ Δ)) (f : Term P (ante Φ) (succ Ψ)) :
    comp (ofTerm (d.prepend hn Φ).route.product) (ofTerm (Rules.mix g f)) =
      ofTerm (Rules.mix (.comp d.route.product g) f) := by
  simp only [Rules.mix,ofTerm_comp,ofTerm_tensor]
  rw [← Laws.assoc,d.prepend_product,Laws.assoc,← Laws.assoc (tensor .conj _ _),
    Laws.tensor_comp,Laws.id_comp]
theorem otherMixR {Φ Ψ Δ : List (NormalForm P)}
    (g : Term P (ante Δ) (succ F)) (f : Term P (ante Φ) (succ Ψ)) :
    comp (ofTerm (Rules.mix g f)) (ofTerm (d.prepend hn Ψ).route.coproduct) =
      ofTerm (Rules.mix (.comp g d.route.coproduct) f) := by
  simp only [Rules.mix,ofTerm_comp,ofTerm_tensor,mix_term]
  rw [Laws.assoc,Laws.assoc,Laws.assoc,d.prepend_coproduct,
    ← Laws.assoc (mix _ _),Laws.mix_nat,Laws.assoc,
    ← Laws.assoc (tensor .conj _ _),Laws.tensor_comp,Laws.comp_id]
end ContractionBlock
end DosenPetric.Reduced.Gentzen
