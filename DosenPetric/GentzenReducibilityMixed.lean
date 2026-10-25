module

public import DosenPetric.GentzenMixedContractionRanks

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.W5.MixedPremiseMix
universe u
variable {P : Type u} {C : NormalForm P} {F K U L : List (NormalForm P)}
variable (p : ContractionSelection C F K) (q : ContractionSelection C U L)

theorem addressed_left {Δ Λ Γ Ξ Θ Ω : List (NormalForm P)}
    (f : G P U Δ) (g : G P F Λ) {cutLeft : G P Γ (C::Ξ)} {root : G P (C::Θ) Ω}
    (a : ProofAddress root (oldL p q f g))
    (hr : ReducibleL cutLeft root a (p.chain q).keep) :
    (newL p q f g).CutFree ∧
    ofTerm (newL p q f g).denote = ofTerm (oldL p q f g).denote ∧
    ofTerm (a.replace (newL p q f g)).denote = ofTerm root.denote ∧
    ∀ {I J : List (NormalForm P)} {v : G P I J}
      (b : ProofAddress (newL p q f g) v) (y : At I C),
      ReducibleL cutLeft (a.replace (newL p q f g)) ((a.inserted _).append b) y →
        v.rho .left y < (oldL p q f g).rho .left (p.chain q).keep := by
  have he:=denoteL p q f g
  refine ⟨?_,he,a.replace_denote _ he,?_⟩
  · have hc:=hr.cutFree
    change (newL p q f g).cutCount=0
    rw [new_countL,←old_countL p q f g]
    exact hc
  · intro I J v b y hv
    exact ReducibilityBoundary.descendants_left a (p.chain q).keep _ (blockedL p q f g)
      (fun z hz => hr.entry_unique z hz) (endpoint_leL p q f g) b y hv

theorem addressed_right {Δ Λ Γ Ξ Θ Ω : List (NormalForm P)}
    (f : G P Δ U) (g : G P Λ F) {root : G P Γ (C::Ξ)} {cutRight : G P (C::Θ) Ω}
    (a : ProofAddress root (oldR p q f g))
    (hr : ReducibleR root cutRight a (p.chain q).keep) :
    (newR p q f g).CutFree ∧
    ofTerm (newR p q f g).denote = ofTerm (oldR p q f g).denote ∧
    ofTerm (a.replace (newR p q f g)).denote = ofTerm root.denote ∧
    ∀ {I J : List (NormalForm P)} {v : G P I J}
      (b : ProofAddress (newR p q f g) v) (y : At J C),
      ReducibleR (a.replace (newR p q f g)) cutRight ((a.inserted _).append b) y →
        v.rho .right y < (oldR p q f g).rho .right (p.chain q).keep := by
  have he:=denoteR p q f g
  refine ⟨?_,he,a.replace_denote _ he,?_⟩
  · have hc:=hr.cutFree
    change (newR p q f g).cutCount=0
    rw [new_countR,←old_countR p q f g]
    exact hc
  · intro I J v b y hv
    exact ReducibilityBoundary.descendants_right a (p.chain q).keep _ (blockedR p q f g)
      (fun z hz => hr.entry_unique z hz) (endpoint_leR p q f g) b y hv

end DosenPetric.Reduced.Gentzen.W5.MixedPremiseMix
