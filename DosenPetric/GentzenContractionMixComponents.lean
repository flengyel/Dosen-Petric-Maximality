module

public import DosenPetric.GentzenContractionAppend
public import DosenPetric.GentzenRuleCongruence

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

theorem mix_term (A B : NormalForm P) : ofTerm (Term.mix A B) = mix A B := rfl

namespace ContractionBlock
variable {F K : List (NormalForm P)} (d : ContractionBlock P F K)
theorem extend_join (o : Op) (Ξ : List (NormalForm P)) :
    (side P o).comp (join o K Ξ) ((d.extend Ξ).route.sideArrow o) =
      (side P o).comp ((sideM P o).tensor (d.route.sideArrow o) ((side P o).id (fold o Ξ)))
        (join o F Ξ) := by
  let C := side P o
  let D := sideD P o
  apply side_ext o
  intro A a
  cases At.cases_append F Ξ a with
  | inl h =>
    obtain ⟨a,rfl⟩ := h
    rw [C.assoc,Route.sideArrow_get,d.extend_before,join_before,
      C.assoc,join_before,← C.assoc,← D.fst_nat,C.assoc,Route.sideArrow_get]
  | inr h =>
    obtain ⟨a,rfl⟩ := h
    rw [C.assoc,Route.sideArrow_get,d.extend_shift,join_shift,
      C.assoc,join_shift,← C.assoc,← D.snd_nat,C.comp_id]

theorem extend_split (o : Op) (Ξ : List (NormalForm P)) :
    (side P o).comp ((d.extend Ξ).route.sideArrow o) (split o F Ξ) =
      (side P o).comp (split o K Ξ)
        ((sideM P o).tensor (d.route.sideArrow o) ((side P o).id (fold o Ξ))) := by
  let C := side P o
  apply DiagonalData.cancel_left (C := C) _ _ (join o K Ξ) (split o K Ξ) (split_join o K Ξ)
  rw [← C.assoc,d.extend_join,C.assoc,join_split,C.comp_id,
    ← C.assoc,join_split,C.id_comp]

theorem extend_product (Ξ : List (NormalForm P)) :
    comp (ofTerm (d.extend Ξ).route.product) (ofTerm (append .conj F Ξ).invTerm) =
      comp (ofTerm (append .conj K Ξ).invTerm) (tensor .conj (ofTerm d.route.product) (id (ante Ξ))) :=
  d.extend_split .conj Ξ
theorem extend_coproduct (Ξ : List (NormalForm P)) :
    comp (ofTerm (append .disj F Ξ).toTerm) (ofTerm (d.extend Ξ).route.coproduct) =
      comp (tensor .disj (ofTerm d.route.coproduct) (id (succ Ξ))) (ofTerm (append .disj K Ξ).toTerm) :=
  d.extend_split .disj Ξ

theorem mixL {Φ Ψ Δ : List (NormalForm P)}
    (f : Term P (ante Φ) (succ Ψ)) (g : Term P (ante F) (succ Δ)) :
    comp (ofTerm (d.extend Φ).route.product) (ofTerm (Rules.mix f g)) =
      ofTerm (Rules.mix f (.comp d.route.product g)) := by
  simp only [Rules.mix,ofTerm_comp,ofTerm_tensor]
  rw [← Laws.assoc,d.extend_product,Laws.assoc,← Laws.assoc (tensor .conj _ _),
    Laws.tensor_comp,Laws.id_comp]

theorem mixR {Φ Ψ Δ : List (NormalForm P)}
    (f : Term P (ante Φ) (succ Ψ)) (g : Term P (ante Δ) (succ F)) :
    comp (ofTerm (Rules.mix f g)) (ofTerm (d.extend Ψ).route.coproduct) =
      ofTerm (Rules.mix f (.comp g d.route.coproduct)) := by
  simp only [Rules.mix,ofTerm_comp,ofTerm_tensor,mix_term]
  rw [Laws.assoc,Laws.assoc,Laws.assoc,d.extend_coproduct,
    ← Laws.assoc (mix _ _),Laws.mix_nat,Laws.assoc,
    ← Laws.assoc (tensor .conj _ _),Laws.tensor_comp,Laws.comp_id]
end ContractionBlock
end DosenPetric.Reduced.Gentzen
