module

public import DosenPetric.GentzenSequentialDisjunctionNative

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.SequentialLogical
universe u
variable {P : Type u}

theorem front_contraction_factor {K U : List (NormalForm P)} {C : NormalForm P}
    (r : Route K (C::U)) (x : At K C) (a : At U C) (p : Route x.erase a.erase)
    (hf : r.get (.here C U) = x) (ha : r.get (.there a) = x)
    (hp : ∀ {E : NormalForm P} (v : At a.erase E), r.get (.there (a.retain v)) = x.retain (p.get v)) :
    x.toHead.route.compose r = (p.head C).compose
      ((SequentialRepair.headBlock C a.erase).route.compose (LogicalDeletion.headUnder [] [C] a).route) := by
  have hm : (LogicalDeletion.headUnder [] [C] a).get (.here C U) = .there (.here C a.erase) := by
    simpa only [At.shift,At.before,List.nil_append] using
      LogicalDeletion.headUnder_middle [] [C] a (.here C [])
  have hs : (LogicalDeletion.headUnder [] [C] a).get (.there a) = .here C (C::a.erase) := by
    simpa only [At.shift,List.nil_append,List.singleton_append] using LogicalDeletion.headUnder_selected [] [C] a
  have ht {E : NormalForm P} (v : At a.erase E) :
      (LogicalDeletion.headUnder [] [C] a).get (.there (a.retain v)) = .there (.there v) := by
    simpa only [At.shift,List.nil_append] using LogicalDeletion.headUnder_fixed [] [C] a v
  apply Route.ext_get
  intro E v
  rw [Route.compose_get,Route.compose_get,Route.compose_get,ExchangeScript.route_get,
    ExchangeScript.route_get]
  cases v with
  | here => rw [hf,At.toHead_get,hm,SequentialRepair.headBlock_route]; rfl
  | there v =>
    by_cases hi : v.index = a.index
    · have he := v.formula_eq a hi
      cases he
      have hv : v = a := At.index_injective v a hi
      cases hv
      rw [ha,At.toHead_get,hs,SequentialRepair.headBlock_route]
      rfl
    · obtain ⟨v,rfl⟩ : ∃ v' : At a.erase E, v = a.retain v' :=
        ⟨a.remove v hi,(a.retain_remove v hi).symm⟩
      rw [hp,At.toHead_get_retain,ht,SequentialRepair.headBlock_route]
      rw [Route.get,Route.get,Route.get_map,Route.get_identity,Route.head_there]

end DosenPetric.Reduced.Gentzen.SequentialLogical
