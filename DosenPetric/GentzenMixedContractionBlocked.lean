module

public import DosenPetric.GentzenMixedContractionRules

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

theorem G.mix_reindex {Γ Δ Θ Λ Γ' Δ' Θ' Λ' : List (NormalForm P)}
    (f : G P Γ Δ) (g : G P Θ Λ) (hΓ : Γ=Γ') (hΔ : Δ=Δ') (hΘ : Θ=Θ') (hΛ : Λ=Λ')
    (h : Θ++Γ=Θ'++Γ') (k : Λ++Δ=Λ'++Δ') :
    (G.mix f g).reindex h k = G.mix (f.reindex hΓ hΔ) (g.reindex hΘ hΛ) := by
  cases hΓ; cases hΔ; cases hΘ; cases hΛ; rfl

theorem G.mix_reindex_inputs {Γ Δ Θ Λ Γ' Δ' Θ' Λ' : List (NormalForm P)}
    (f : G P Γ Δ) (g : G P Θ Λ) (hΓ : Γ=Γ') (hΔ : Δ=Δ') (hΘ : Θ=Θ') (hΛ : Λ=Λ') :
    G.mix (f.reindex hΓ hΔ) (g.reindex hΘ hΛ) =
      (G.mix f g).reindex (by cases hΓ; cases hΘ; rfl) (by cases hΔ; cases hΛ; rfl) := by
  cases hΓ; cases hΔ; cases hΘ; cases hΛ; rfl

namespace W5.MixedPremiseMix
variable {C : NormalForm P} {F K U L : List (NormalForm P)}
variable (p : ContractionSelection C F K) (q : ContractionSelection C U L)

theorem blockedL {Δ Λ : List (NormalForm P)} (f : G P U Δ) (g : G P F Λ) :
    BlockedL (newL p q f g) := by
  have h := BlockedL.gammaMix C (gaps q.gs) q.tail (gaps p.gs) p.tail Δ Λ
    ((q.performL Δ f).reindex q.lower.symm rfl)
    ((p.performL Λ g).reindex p.lower.symm rfl)
  have he := h.reindex (p.mergeBlock q).lower rfl
  simpa only [newL,middleL,ContractionBlock.applyL,ContractionSelection.mergeBlock,
    BlockedSource.left2,G.mix_reindex_inputs,G.reindex_trans] using he

theorem blockedR {Δ Λ : List (NormalForm P)} (f : G P Δ U) (g : G P Λ F) :
    BlockedR (newR p q f g) := by
  have h := BlockedR.gammaMix C Δ Λ (gaps q.gs) q.tail (gaps p.gs) p.tail
    ((q.performR Δ f).reindex rfl q.lower.symm)
    ((p.performR Λ g).reindex rfl p.lower.symm)
  have he := h.reindex rfl (p.mergeBlock q).lower
  simpa only [newR,middleR,ContractionBlock.applyR,ContractionSelection.mergeBlock,
    BlockedSource.right2,G.mix_reindex_inputs,G.reindex_trans] using he

end W5.MixedPremiseMix
end DosenPetric.Reduced.Gentzen
