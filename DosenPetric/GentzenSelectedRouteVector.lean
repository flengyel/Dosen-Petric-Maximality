module

public import DosenPetric.GentzenScriptRoutes

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.Route
universe u
variable {P : Type u}

theorem selected_get_factor {K U : List (NormalForm P)} {C : NormalForm P}
    (r : Route K U) (x : At K C) (a : At U C) (p : Route x.erase a.erase)
    (ha : r.get a = x)
    (hp : ∀ {B : NormalForm P} (v : At a.erase B),
      r.get (a.retain v) = x.retain (p.get v))
    {B : NormalForm P} (v : At U B) :
    x.toHead.get (r.get v) = (p.head C).get (a.toHead.get v) := by
  by_cases hi : v.index = a.index
  · have he := v.formula_eq a hi
    cases he
    have hv : v = a := At.index_injective v a hi
    cases hv
    rw [ha,At.toHead_get,At.toHead_get,head_here]
  · obtain ⟨v,rfl⟩ : ∃ v' : At a.erase B, v = a.retain v' :=
      ⟨a.remove v hi,(a.retain_remove v hi).symm⟩
    rw [hp,At.toHead_get_retain,At.toHead_get_retain,head_there]

theorem selected_blocks_factor {K F U : List (NormalForm P)} {C : NormalForm P}
    (r : Route K (F++U)) (x : At K C) (a : At F C) (b : At U C)
    (p : Route x.erase a.erase) (q : Route x.erase b.erase)
    (ha : r.firstBlock.get a = x) (hb : r.secondBlock.get b = x)
    (hp : ∀ {B : NormalForm P} (v : At a.erase B),
      r.firstBlock.get (a.retain v) = x.retain (p.get v))
    (hq : ∀ {B : NormalForm P} (v : At b.erase B),
      r.secondBlock.get (b.retain v) = x.retain (q.get v)) :
    x.toHead.route.compose r =
      ((p.head C).append (q.head C)).compose (a.toHead.route.parallel b.toHead.route) := by
  apply ext_get
  intro B v
  cases At.cases_append F U v with
  | inl hv =>
    obtain ⟨v,rfl⟩ := hv
    rw [compose_get,ExchangeScript.route_get,compose_get,parallel_before,append_before,
      ExchangeScript.route_get]
    simpa only [firstBlock_get] using selected_get_factor r.firstBlock x a p ha hp v
  | inr hv =>
    obtain ⟨v,rfl⟩ := hv
    rw [compose_get,ExchangeScript.route_get,compose_get,parallel_shift,append_shift,
      ExchangeScript.route_get]
    simpa only [secondBlock_get] using selected_get_factor r.secondBlock x b q hb hq v

end DosenPetric.Reduced.Gentzen.Route
