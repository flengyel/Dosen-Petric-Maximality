module

public import DosenPetric.GentzenReductionStatements

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u} {C : NormalForm P} {Γ Δ Θ Λ U V : List (NormalForm P)}
variable {f : G P Γ (C::Δ)} {g : G P (C::Θ) Λ} {w h : G P U V}

/-- An internally constructed strict endpoint reduction suffices for every
eligible contraction in the replacement. This lemma supplies no candidate. -/
theorem ReducesL.of_strict (x : At U C) (hc : w.CutFree→h.CutFree)
    (he : ofTerm h.denote=ofTerm w.denote) (hk : h.rho .left x<w.rho .left x) :
    ReducesL f g w x := by
  intro a hr
  refine ⟨h,hc hr.cutFree,he,?_⟩
  intro I J v b y hv
  exact ReducibilityBoundary.strict_left a x hr hk b y hv

theorem ReducesR.of_strict (x : At V C) (hc : w.CutFree→h.CutFree)
    (he : ofTerm h.denote=ofTerm w.denote) (hk : h.rho .right x<w.rho .right x) :
    ReducesR f g w x := by
  intro a hr
  refine ⟨h,hc hr.cutFree,he,?_⟩
  intro I J v b y hv
  exact ReducibilityBoundary.strict_right a x hr hk b y hv
end DosenPetric.Reduced.Gentzen
