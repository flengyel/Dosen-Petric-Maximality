module

public import DosenPetric.GentzenParallelRoutes
public import DosenPetric.GentzenContractionMixComponents

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u} {C : NormalForm P} {F K U L : List (NormalForm P)}
namespace ContractionSelection
variable (p : ContractionSelection C F K) (q : ContractionSelection C U L)

theorem chain_square (o : Op) :
    (p.chain q).route.sideArrow o =
      (side P o).comp ((p.mergeBlock q).route.sideArrow o)
        ((p.route.parallel q.route).sideArrow o) := by
  let D := side P o
  apply side_ext o
  intro A a
  rw [D.assoc,Route.sideArrow_get,Route.sideArrow_get]
  cases At.cases_append F U a with
  | inl h =>
    obtain ⟨a,rfl⟩ := h
    rw [Route.sideArrow_get,chain_before,Route.parallel_before,←merge_route]
  | inr h =>
    obtain ⟨a,rfl⟩ := h
    rw [Route.sideArrow_get,chain_shift,Route.parallel_shift,←merge_route,merge_shift]

theorem parallel_mixL {Γ Δ : List (NormalForm P)}
    (f : Term P (ante U) (succ Γ)) (g : Term P (ante F) (succ Δ)) :
    comp (ofTerm (p.route.parallel q.route).product) (ofTerm (Rules.mix f g)) =
      ofTerm (Rules.mix (.comp q.route.product f) (.comp p.route.product g)) := by
  have h := Route.parallel_split .conj p.route q.route
  change comp (ofTerm (p.route.parallel q.route).product) (ofTerm (append .conj F U).invTerm) =
    comp (ofTerm (append .conj K L).invTerm)
      (tensor .conj (ofTerm p.route.product) (ofTerm q.route.product)) at h
  simp only [Rules.mix,ofTerm_comp,ofTerm_tensor]
  rw [←Laws.assoc,h,Laws.assoc,←Laws.assoc (tensor .conj _ _),Laws.tensor_comp]

theorem parallel_mixR {Γ Δ : List (NormalForm P)}
    (f : Term P (ante Γ) (succ U)) (g : Term P (ante Δ) (succ F)) :
    comp (ofTerm (Rules.mix f g)) (ofTerm (p.route.parallel q.route).coproduct) =
      ofTerm (Rules.mix (.comp f q.route.coproduct) (.comp g p.route.coproduct)) := by
  have h := Route.parallel_split .disj p.route q.route
  change comp (ofTerm (append .disj F U).toTerm) (ofTerm (p.route.parallel q.route).coproduct) =
    comp (tensor .disj (ofTerm p.route.coproduct) (ofTerm q.route.coproduct))
      (ofTerm (append .disj K L).toTerm) at h
  simp only [Rules.mix,ofTerm_comp,ofTerm_tensor,mix_term]
  rw [Laws.assoc,Laws.assoc,Laws.assoc,h,←Laws.assoc (mix _ _),Laws.mix_nat,
    Laws.assoc,←Laws.assoc (tensor .conj _ _),Laws.tensor_comp]

end ContractionSelection
end DosenPetric.Reduced.Gentzen
