module

public import DosenPetric.GentzenSourceLogicalRankBounds

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.W6.SourceLeft
universe u
variable {P : Type u} {A B : NormalForm P} {F K U L : List (NormalForm P)}
variable (p : ContractionSelection (.disj A B) F K) (q : ContractionSelection (.disj A B) U L)

theorem addressed_left {Δ Λ Γ Ξ Θ Ω : List (NormalForm P)}
    (f : G P (F++[A]) Δ) (g : G P (U++[B]) Λ)
    {cutLeft : G P Γ (.disj A B::Ξ)} {root : G P (.disj A B::Θ) Ω}
    (a : ProofAddress root (old p q f g))
    (hr : ReducibleL cutLeft root a (p.sourceKeep q)) :
    (repair p q f g).CutFree ∧
    ofTerm (repair p q f g).denote=ofTerm (old p q f g).denote ∧
    ofTerm (a.replace (repair p q f g)).denote=ofTerm root.denote ∧
    ∀ {I J : List (NormalForm P)} {v : G P I J}
      (b : ProofAddress (repair p q f g) v) (y : At I (.disj A B)),
      ReducibleL cutLeft (a.replace (repair p q f g)) ((a.inserted _).append b) y →
        v.rho .left y<(old p q f g).rho .left (p.sourceKeep q) := by
  have he:=denote p q f g
  refine ⟨?_,he,a.replace_denote _ he,?_⟩
  · have hc:=hr.cutFree
    change (repair p q f g).cutCount=0
    rw [repair_count,←old_count p q f g]
    exact hc
  · intro I J v b y hv
    exact ReducibilityBoundary.descendants_left a (p.sourceKeep q) _ (repair_blocked p q f g)
      (fun z hz => hr.entry_unique z hz) (endpoint_le p q f g) b y hv

end DosenPetric.Reduced.Gentzen.W6.SourceLeft
