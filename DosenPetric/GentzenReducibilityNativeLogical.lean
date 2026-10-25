module

public import DosenPetric.GentzenNativeLogicalBounds

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.W6.NativeLeft
universe u
variable {P : Type u} {A B : NormalForm P} {F K U L : List (NormalForm P)}
variable (p : ContractionSelection (.disj A B) F K) (q : ContractionSelection (.disj A B) U L)

theorem addressed_left {Δ Λ Γ Ξ Θ Ω : List (NormalForm P)}
    (f : G P (A::F) Δ) (g : G P (B::U) Λ)
    {cutLeft : G P Γ (.disj A B::Ξ)} {root : G P (.disj A B::Θ) Ω}
    (a : ProofAddress root (old p q f g))
    (hr : ReducibleL cutLeft root a (p.chain q).keep) :
    (repair p q f g).CutFree ∧
    ofTerm (repair p q f g).denote=ofTerm (old p q f g).denote ∧
    ofTerm (a.replace (repair p q f g)).denote=ofTerm root.denote ∧
    ∀ {I J : List (NormalForm P)} {v : G P I J}
      (b : ProofAddress (repair p q f g) v) (y : At I (.disj A B)),
      ReducibleL cutLeft (a.replace (repair p q f g)) ((a.inserted _).append b) y →
        v.rho .left y<(old p q f g).rho .left (p.chain q).keep := by
  have he:=denote p q f g
  refine ⟨?_,he,a.replace_denote _ he,?_⟩
  · apply (repair_cutFree p q f g).mpr
    have hc:=hr.cutFree
    change (old p q f g).cutCount=0 at hc
    rw [old_count] at hc
    exact Nat.add_eq_zero_iff.mp hc
  · intro I J v b y hv
    obtain ⟨z,hz,ha⟩ := (a.replacement_cluster_iff (repair p q f g) b .left
      (.here (.disj A B) Θ) y).mp hv.2.1.1
    have hx : z=(p.chain q).keep := hr.entry_unique z ha
    cases hx
    exact (repair_bound p q f g).bound b (p.chain q).keep rfl y hz hv.2.1.2 hv.2.2.1

end DosenPetric.Reduced.Gentzen.W6.NativeLeft
