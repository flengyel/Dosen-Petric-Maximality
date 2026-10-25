module

public import DosenPetric.GentzenOneDisjunctionAntecedentRanks

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u} {A B C : NormalForm P} {F K U L Γ Θ Φ Ξ Ω Λ : List (NormalForm P)}
namespace W5.OneDisjunctionAntecedent

theorem reducesFirst (p : ContractionSelection C F K) (hn : 2≤p.arity)
    (f : G P (A::F) Γ) (g : G P (B::U) Θ)
    (cutLeft : G P Φ (C::Ξ)) (root : G P (C::Ω) Λ) :
    ReducesL cutLeft root (oldFirst p f g) (.there (p.keep.before U)) := by
  intro a hr
  have he:=denoteFirst p f g
  refine ⟨repairFirst p f g,?_,he,?_⟩
  · apply (repair_cutFreeFirst p f g).mpr
    have hc:=hr.cutFree
    change (oldFirst p f g).cutCount=0 at hc
    rw [old_countFirst] at hc
    exact Nat.add_eq_zero_iff.mp hc
  · intro I J v b y hv
    exact ReducibilityBoundary.strict_left a _ hr (endpoint_ltFirst p f g hn) b y hv

theorem reducesSecond (q : ContractionSelection C U L) (hn : 2≤q.arity)
    (f : G P (A::F) Γ) (g : G P (B::U) Θ)
    (cutLeft : G P Φ (C::Ξ)) (root : G P (C::Ω) Λ) :
    ReducesL cutLeft root (oldSecond q f g) (.there (At.shift F q.keep)) := by
  intro a hr
  have he:=denoteSecond q f g
  refine ⟨repairSecond q f g,?_,he,?_⟩
  · apply (repair_cutFreeSecond q f g).mpr
    have hc:=hr.cutFree
    change (oldSecond q f g).cutCount=0 at hc
    rw [old_countSecond] at hc
    exact Nat.add_eq_zero_iff.mp hc
  · intro I J v b y hv
    exact ReducibilityBoundary.strict_left a _ hr (endpoint_ltSecond q f g hn) b y hv
end W5.OneDisjunctionAntecedent
end DosenPetric.Reduced.Gentzen
