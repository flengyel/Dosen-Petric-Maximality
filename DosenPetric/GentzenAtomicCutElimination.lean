module

public import DosenPetric.GentzenPositionalCutBase

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace PositionalCut

/-- Exhaust every literal, zero, thinning and constant cut at the least selected rank. -/
theorem atomic_rank_two {Γ Δ Θ Λ : List (NormalForm P)} {C : NormalForm P}
    (f : G P Γ Δ) (x : At Δ C) (g : G P Θ Λ) (y : At Θ C)
    (hf : f.CutFree) (hg : g.CutFree) (af : f.Atomized) (ag : g.Atomized)
    (hc : AtomicFormula C) (hr : rank f x g y = 2) : Eliminated f x g y := by
  obtain ⟨hx,hy⟩ := (rank_two_iff_leaves f x g y).mp hr
  have rx := rightLeaf_complete f af x hx
  have ly := leftLeaf_complete g ag y hy
  cases rx with
  | identity l =>
    cases ly with
    | identity => exact ⟨G.identity l, rfl, True.intro, (CutBase.identity_identity l).symm⟩
    | zero => exact ⟨G.zero l, rfl, True.intro, (CutBase.identity_zero l).symm⟩
    | @thin F U V C g ha => exact endomorphism_thin _ (G.identity l) g hg ag.2 hc
  | zero l =>
    cases ly with
    | identity => exact ⟨G.zero l, rfl, True.intro, (CutBase.zero_identity l).symm⟩
    | zero => exact ⟨G.zero l, rfl, True.intro, (CutBase.zero_zero l).symm⟩
    | @thin F U V C g ha => exact endomorphism_thin _ (G.zero l) g hg ag.2 hc
  | top =>
    cases ly with
    | @thin F U V C g ha => exact top_thin F U _ g hg ag.2
  | @thin Γ Δ Λ C f ha =>
    cases ly with
    | identity l => exact thin_endomorphism _ f (G.identity l) hf af.2 hc
    | zero l => exact thin_endomorphism _ f (G.zero l) hf af.2 hc
    | bot => exact thin_bot Γ Δ Λ f hf af.2
    | @thin F U V C g hb => exact thin_thin Γ Δ Λ F U _ _ f g hf hg af.2 ag.2
    | conj => cases hc
    | disj => cases hc
  | conj => cases hc
  | disj => cases hc

end PositionalCut
end DosenPetric.Reduced.Gentzen
