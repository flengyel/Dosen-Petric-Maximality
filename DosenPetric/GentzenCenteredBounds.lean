module

public import DosenPetric.GentzenContextNormalizationLaws
public import DosenPetric.GentzenFixedHeadLogicalBounds

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.ExchangeScript
universe u
variable {P : Type u} {C : NormalForm P} {F M Δ : List (NormalForm P)} {k : Nat}
variable (v : ExchangeScript P (C::M) F) (x : At F C)
variable (hv : v.get x=.here C M)

include hv in
theorem bound_at_left (g : G P F Δ) (hk : g.rho .left x<k) :
    ContractionBound .left C k (v.left g) (fun a=>a.index=0) := by
  apply v.bound_left
  apply ContractionBound.bounded
  intro a ha
  have he : v.get a=.here C M:=At.index_injective _ _ ha
  have hx : a=x:=v.injective a x (he.trans hv.symm)
  cases hx;exact hk

include hv in
theorem bound_at_right (g : G P Δ F) (hk : g.rho .right x<k) :
    ContractionBound .right C k (v.right g) (fun a=>a.index=0) := by
  apply v.bound_right
  apply ContractionBound.bounded
  intro a ha
  have he : v.get a=.here C M:=At.index_injective _ _ ha
  have hx : a=x:=v.injective a x (he.trans hv.symm)
  cases hx;exact hk

include hv in
theorem inverse_bound_left (g : G P (C::M) Δ)
    (h : ContractionBound .left C k g (fun a=>a.index=0)) :
    ContractionBound .left C k (v.inverse.left g) (fun a=>a=x) := by
  apply v.inverse.bound_left
  apply h.mono
  intro a ha
  have he:=congrArg v.get ha
  have he' : a=.here C M:=(v.get_inverse a).symm.trans (he.trans hv)
  exact congrArg At.index he'

include hv in
theorem inverse_bound_right (g : G P Δ (C::M))
    (h : ContractionBound .right C k g (fun a=>a.index=0)) :
    ContractionBound .right C k (v.inverse.right g) (fun a=>a=x) := by
  apply v.inverse.bound_right
  apply h.mono
  intro a ha
  have he:=congrArg v.get ha
  have he' : a=.here C M:=(v.get_inverse a).symm.trans (he.trans hv)
  exact congrArg At.index he'
end DosenPetric.Reduced.Gentzen.ExchangeScript
