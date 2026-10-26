module

public import DosenPetric.GentzenMaskCoordinates

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.ContractionSelection
universe u
variable {P : Type u} {C : NormalForm P} {F K : List (NormalForm P)}

def normalize (p : ContractionSelection C F K) : ExchangeScript P (C::p.mask.erased) K :=
  p.center.reindex (congrArg (List.cons C) p.mask_erased.symm) rfl

theorem normalize_keep (p : ContractionSelection C F K) :
    p.normalize.get p.keep=.here C p.mask.erased := by
  apply At.index_injective
  change ((p.center.get p.keep).cast _).index=0
  rw [At.index_cast,p.center_keep]
  rfl

theorem center_index (p : ContractionSelection C F K) {A : NormalForm P} (a : At F A) :
    (p.center.get (p.route.get a)).index=if p.mask.picked a then 0 else p.mask.offset a+1 := by
  rw [←Route.get_map (fun {A} b=>p.center.get b) p.route a]
  rw [p.route_fill,SelectionMask.fill_map]
  apply p.mask.fill_index _ _ 1 (congrArg At.index p.center_keep)
  intro B b
  rw [Route.get_map,Route.get_cast]
  change (p.center.get (p.erasedRoute.get (b.cast p.mask_erased))).index=b.index+1
  rw [p.center_erased,At.index,At.index_cast]

theorem normalize_index (p : ContractionSelection C F K) {A : NormalForm P} (a : At F A) :
    (p.normalize.get (p.route.get a)).index=if p.mask.picked a then 0 else p.mask.offset a+1 := by
  change ((p.center.get (p.route.get a)).cast _).index=_
  rw [At.index_cast]
  exact p.center_index a
end DosenPetric.Reduced.Gentzen.ContractionSelection
