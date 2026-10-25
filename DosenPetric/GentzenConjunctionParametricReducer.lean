module

public import DosenPetric.GentzenOneConjunctionRanks
public import DosenPetric.GentzenReductionStatements

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u} {A B C : NormalForm P} {F K U L Γ Θ Φ Ξ Ω Λ : List (NormalForm P)}
namespace W5.ParametricConjunction

theorem reduces (p : ContractionSelection C F K) (q : ContractionSelection C U L)
    (f : G P Γ (A::F)) (g : G P Θ (B::U))
    (root : G P Φ (C::Ξ)) (cutRight : G P (C::Ω) Λ) :
    ReducesR root cutRight (old p q f g) (.there (p.chain q).keep) := by
  intro a hr
  have he:=denote p q f g
  refine ⟨repair p q f g,?_,he,?_⟩
  · apply (repair_cutFree p q f g).mpr
    have hc:=hr.cutFree
    change (old p q f g).cutCount=0 at hc
    rw [old_count] at hc
    exact Nat.add_eq_zero_iff.mp hc
  · intro I J v b y hv
    exact ReducibilityBoundary.descendants_right a (.there (p.chain q).keep) _ (blocked p q f g)
      (fun z hz => hr.entry_unique z hz) (endpoint_le p q f g) b y hv
end W5.ParametricConjunction
namespace W5.OneConjunction

theorem reducesFirst (p : ContractionSelection C F K) (hn : 2≤p.arity)
    (f : G P Γ (A::F)) (g : G P Θ (B::U))
    (root : G P Φ (C::Ξ)) (cutRight : G P (C::Ω) Λ) :
    ReducesR root cutRight (oldFirst p f g) (.there (p.keep.before U)) := by
  intro a hr
  have he:=denoteFirst p f g
  refine ⟨repairFirst p f g,?_,he,?_⟩
  · apply (repair_cutFreeFirst p f g).mpr
    have hc:=hr.cutFree
    change (oldFirst p f g).cutCount=0 at hc
    rw [old_countFirst] at hc
    exact Nat.add_eq_zero_iff.mp hc
  · intro I J v b y hv
    exact ReducibilityBoundary.strict_right a _ hr (endpoint_ltFirst p f g hn) b y hv

theorem reducesSecond (q : ContractionSelection C U L) (hn : 2≤q.arity)
    (f : G P Γ (A::F)) (g : G P Θ (B::U))
    (root : G P Φ (C::Ξ)) (cutRight : G P (C::Ω) Λ) :
    ReducesR root cutRight (oldSecond q f g) (.there (At.shift F q.keep)) := by
  intro a hr
  have he:=denoteSecond q f g
  refine ⟨repairSecond q f g,?_,he,?_⟩
  · apply (repair_cutFreeSecond q f g).mpr
    have hc:=hr.cutFree
    change (oldSecond q f g).cutCount=0 at hc
    rw [old_countSecond] at hc
    exact Nat.add_eq_zero_iff.mp hc
  · intro I J v b y hv
    exact ReducibilityBoundary.strict_right a _ hr (endpoint_ltSecond q f g hn) b y hv
end W5.OneConjunction
end DosenPetric.Reduced.Gentzen
