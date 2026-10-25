module

public import DosenPetric.GentzenHeadLogicalRankBounds

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.W6.HeadRight
universe u
variable {P : Type u} {A B : NormalForm P} {F K U L : List (NormalForm P)}
variable (p : ContractionSelection (.conj A B) F K) (q : ContractionSelection (.conj A B) U L)

theorem addressed_right {Γ Θ Φ Δ Ξ Λ : List (NormalForm P)}
    (f : G P Γ (A::F)) (g : G P Θ (B::U))
    {root : G P Φ (.conj A B::Δ)} {cutRight : G P (.conj A B::Ξ) Λ}
    (a : ProofAddress root (old p q f g))
    (hr : ReducibleR root cutRight a (p.chain q).keep) :
    (repair p q f g).CutFree ∧
    ofTerm (repair p q f g).denote=ofTerm (old p q f g).denote ∧
    ofTerm (a.replace (repair p q f g)).denote=ofTerm root.denote ∧
    ∀ {I J : List (NormalForm P)} {v : G P I J}
      (b : ProofAddress (repair p q f g) v) (y : At J (.conj A B)),
      ReducibleR (a.replace (repair p q f g)) cutRight ((a.inserted _).append b) y →
        v.rho .right y<(old p q f g).rho .right (p.chain q).keep := by
  have he:=denote p q f g
  refine ⟨?_,he,a.replace_denote _ he,?_⟩
  · have hc:=hr.cutFree
    change (repair p q f g).cutCount=0
    rw [repair_count,←old_count p q f g]
    exact hc
  · intro I J v b y hv
    exact ReducibilityBoundary.descendants_right a (p.chain q).keep _ (repair_blocked p q f g)
      (fun z hz => hr.entry_unique z hz) (endpoint_le p q f g) b y hv

end DosenPetric.Reduced.Gentzen.W6.HeadRight
