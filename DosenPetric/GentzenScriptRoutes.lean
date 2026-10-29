module

public import DosenPetric.GentzenBlockedLeftDisjEquation
public import DosenPetric.GentzenSelectionRouteExtension

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace ExchangeScript

def route {F U : List (NormalForm P)} (p : ExchangeScript P F U) : Route F U :=
  (Route.identity U).map (fun a => p.get a)

theorem route_get {F U : List (NormalForm P)} (p : ExchangeScript P F U)
    {A : NormalForm P} (a : At U A) : p.route.get a = p.get a := by
  rw [route,Route.get_map,Route.get_identity]

theorem route_arrow {F U : List (NormalForm P)} (p : ExchangeScript P F U) (o : Op) :
    p.route.sideArrow o = p.arrow o := by
  apply side_ext o
  intro A a
  rw [Route.sideArrow_get,component,route_get]

theorem suffix_route {F U : List (NormalForm P)} (p : ExchangeScript P F U) (W : List (NormalForm P))
    (o : Op) : (p.structural.suffixFixed W).arrow o = (p.route.parallel (Route.identity W)).sideArrow o := by
  apply side_ext o
  intro A a
  rw [StructuralProgram.component,Route.sideArrow_get]
  cases At.cases_append U W a with
  | inl ha =>
    obtain ⟨a,rfl⟩ := ha
    rw [StructuralProgram.suffixFixed_before,structural_get,Route.parallel_before,route_get]
  | inr ha =>
    obtain ⟨a,rfl⟩ := ha
    rw [StructuralProgram.suffixFixed_shift,Route.parallel_shift,Route.get_identity]

end ExchangeScript
namespace Route

theorem parallel_compose_fixed {F K U : List (NormalForm P)} (p : Route K U) (q : Route U F)
    (W : List (NormalForm P)) :
    (p.parallel (identity W)).compose (q.parallel (identity W)) = (p.compose q).parallel (identity W) := by
  apply ext_get
  intro A a
  cases At.cases_append F W a with
  | inl ha =>
    obtain ⟨a,rfl⟩ := ha
    rw [compose_get,parallel_before,parallel_before,parallel_before,compose_get]
  | inr ha =>
    obtain ⟨a,rfl⟩ := ha
    rw [compose_get,parallel_shift,parallel_shift,parallel_shift,get_identity,get_identity]

end Route
namespace LogicalDeletion

theorem headBefore_route {F : List (NormalForm P)} {C : NormalForm P} (a : At F C)
    (W : List (NormalForm P)) (o : Op) :
    (headBefore a W).arrow o = (a.toHead.route.parallel (Route.identity W)).sideArrow o := by
  rw [BinaryMix.headBefore_structural]
  exact a.toHead.suffix_route W o

end LogicalDeletion
end DosenPetric.Reduced.Gentzen
