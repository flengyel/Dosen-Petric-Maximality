module

public import DosenPetric.GentzenSequentialLogicalScripts

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.SequentialLogical
universe u
variable {P : Type u}

theorem duplicated_head_terminal {K F : List (NormalForm P)} (C : NormalForm P) (p : Route K F) :
    (p.head C).append (.cons (.here C K) .nil) =
      (p.head C).compose ((SequentialRepair.headBlock C F).route.compose
        ((BinaryMix.swapWhole F [C]).consFixed C).route) := by
  apply Route.ext_get
  intro A a
  cases At.cases_append (C::F) [C] a with
  | inl ha =>
    obtain ⟨a,rfl⟩ := ha
    rw [Route.append_before,Route.compose_get,Route.compose_get,ExchangeScript.route_get]
    cases a with
    | here =>
      rw [At.before,ExchangeScript.consFixed_here,SequentialRepair.headBlock_route]
      rfl
    | there a =>
      rw [At.before,ExchangeScript.consFixed_there,BinaryMix.swapWhole_before,SequentialRepair.headBlock_route]
      rw [At.shift,Route.get,Route.get,Route.get_map,Route.get_identity]
      rfl
  | inr ha =>
    obtain ⟨a,rfl⟩ := ha
    cases a with
    | here =>
      rw [Route.append_shift,Route.compose_get,Route.compose_get,ExchangeScript.route_get]
      rw [At.shift,ExchangeScript.consFixed_there,BinaryMix.swapWhole_shift,
        SequentialRepair.headBlock_route]
      rfl
    | there a => cases a

end DosenPetric.Reduced.Gentzen.SequentialLogical
