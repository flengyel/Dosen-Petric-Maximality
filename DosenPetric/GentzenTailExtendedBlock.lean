module

public import DosenPetric.GentzenSelectionRouteExtension

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.ContractionBlock
universe u
variable {P : Type u} {F K : List (NormalForm P)}

theorem extend_route (d : ContractionBlock P F K) (Ξ : List (NormalForm P)) :
    (d.extend Ξ).route=d.route.parallel (Route.identity Ξ) := by
  apply Route.ext_get
  intro A a
  cases At.cases_append F Ξ a with
  | inl h => obtain ⟨a,rfl⟩:=h; rw [d.extend_before,Route.parallel_before]
  | inr h => obtain ⟨a,rfl⟩:=h; rw [d.extend_shift,Route.parallel_shift,Route.get_identity]
end DosenPetric.Reduced.Gentzen.ContractionBlock
