module

public import DosenPetric.GentzenOneHeadConjunctionRanks
public import DosenPetric.GentzenConjunctionParametricReducer
public import DosenPetric.GentzenReducibilityHeadLogical

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u} {A B : NormalForm P} {F K U L Γ Θ Φ Ξ Ω Λ : List (NormalForm P)}
namespace W6.OneHeadConjunction

theorem reducesFirst (p : ContractionSelection (.conj A B) F K)
    (f : G P Γ (A::F)) (g : G P Θ (B::U))
    (root : G P Φ (.conj A B::Ξ)) (cutRight : G P (.conj A B::Ω) Λ) :
    ReducesR root cutRight (oldFirst p f g) (p.keep.before U) := by
  intro a hr
  have he:=denoteFirst p f g
  refine ⟨repairFirst p f g,?_,he,?_⟩
  · have hc:=hr.cutFree
    change (oldFirst p f g).cutCount=0 at hc
    rw [old_countFirst] at hc
    change (repairFirst p f g).cutCount=0
    rw [repair_countFirst]
    exact hc
  · intro I J v b y hv
    exact ReducibilityBoundary.descendants_right a (p.keep.before U) _ (blockedFirst p f g)
      (fun z hz => hr.entry_unique z hz) (endpoint_leFirst p f g) b y hv

theorem reducesSecond (q : ContractionSelection (.conj A B) U L)
    (f : G P Γ (A::F)) (g : G P Θ (B::U))
    (root : G P Φ (.conj A B::Ξ)) (cutRight : G P (.conj A B::Ω) Λ) :
    ReducesR root cutRight (oldSecond q f g) (At.shift F q.keep) := by
  intro a hr
  have he:=denoteSecond q f g
  refine ⟨repairSecond q f g,?_,he,?_⟩
  · have hc:=hr.cutFree
    change (oldSecond q f g).cutCount=0 at hc
    rw [old_countSecond] at hc
    change (repairSecond q f g).cutCount=0
    rw [repair_countSecond]
    exact hc
  · intro I J v b y hv
    exact ReducibilityBoundary.descendants_right a (At.shift F q.keep) _ (blockedSecond q f g)
      (fun z hz => hr.entry_unique z hz) (endpoint_leSecond q f g) b y hv
end W6.OneHeadConjunction
namespace W6.HeadRight

theorem reduces (p : ContractionSelection (.conj A B) F K) (q : ContractionSelection (.conj A B) U L)
    (f : G P Γ (A::F)) (g : G P Θ (B::U))
    (root : G P Φ (.conj A B::Ξ)) (cutRight : G P (.conj A B::Ω) Λ) :
    ReducesR root cutRight (old p q f g) (p.chain q).keep := by
  intro a hr
  have h:=addressed_right p q f g a hr
  exact ⟨repair p q f g,h.1,h.2.1,h.2.2.2⟩
end W6.HeadRight
end DosenPetric.Reduced.Gentzen
