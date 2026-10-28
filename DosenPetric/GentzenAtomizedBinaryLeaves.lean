module

public import DosenPetric.GentzenAllInputReducers
public import DosenPetric.GentzenAtomizedRouting

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.W5.OneConjunctionAntecedent
universe u
variable {P : Type u} {A B C : NormalForm P} {F K U L Δ Λ : List (NormalForm P)}
section First
variable (p : ContractionSelection C F K) (f : G P F (A::Δ)) (g : G P U (B::Λ))
theorem reducesFirst_atomized {Φ Ξ Ω Ψ : List (NormalForm P)} (hn : 2≤p.arity)
    (cutLeft : G P Φ (C::Ξ)) (root : G P (C::Ω) Ψ) :
    AtomizedReducesL cutLeft root (oldFirst p f g) (p.keep.before U) := by
  intro hat a hr
  refine ⟨repairFirst p f g,?_,?_,denoteFirst p f g,?_⟩
  · have hc:=hr.cutFree
    change (oldFirst p f g).cutCount=0 at hc
    rw [old_countFirst] at hc
    change (repairFirst p f g).cutCount=0
    rw [repair_countFirst]; exact hc
  · have hin : f.Atomized ∧ g.Atomized := by
      simpa only [oldFirst,ContractionSelection.performL_atomized,
        ContractionSelection.performR_atomized,G.Atomized] using hat
    simpa only [repairFirst,ContractionBlock.atomizedL,ContractionBlock.atomizedR,
      G.atomized_reindex,G.Atomized,ContractionSelection.performL_atomized,
      ContractionSelection.performR_atomized] using hin
  · intro I J v b y hv
    exact ReducibilityBoundary.strict_left a _ hr (endpoint_ltFirst p f g hn) b y hv
end First
section Second
variable (q : ContractionSelection C U L) (f : G P F (A::Δ)) (g : G P U (B::Λ))
theorem reducesSecond_atomized {Φ Ξ Ω Ψ : List (NormalForm P)} (hn : 2≤q.arity)
    (cutLeft : G P Φ (C::Ξ)) (root : G P (C::Ω) Ψ) :
    AtomizedReducesL cutLeft root (oldSecond q f g) (At.shift F q.keep) := by
  intro hat a hr
  refine ⟨repairSecond q f g,?_,?_,denoteSecond q f g,?_⟩
  · have hc:=hr.cutFree
    change (oldSecond q f g).cutCount=0 at hc
    rw [old_countSecond] at hc
    change (repairSecond q f g).cutCount=0
    rw [repair_countSecond]; exact hc
  · have hin : f.Atomized ∧ g.Atomized := by
      simpa only [oldSecond,ContractionSelection.performL_atomized,
        ContractionSelection.performR_atomized,G.Atomized] using hat
    simpa only [repairSecond,ContractionBlock.atomizedL,ContractionBlock.atomizedR,
      G.atomized_reindex,G.Atomized,ContractionSelection.performL_atomized,
      ContractionSelection.performR_atomized] using hin
  · intro I J v b y hv
    exact ReducibilityBoundary.strict_left a _ hr (endpoint_ltSecond q f g hn) b y hv
end Second
end DosenPetric.Reduced.Gentzen.W5.OneConjunctionAntecedent

namespace DosenPetric.Reduced.Gentzen.W5.ConjunctionAntecedent
universe u
variable {P : Type u} {A B C : NormalForm P} {F K U L Δ Λ : List (NormalForm P)}
variable (p : ContractionSelection C F K) (q : ContractionSelection C U L)
variable (f : G P F (A::Δ)) (g : G P U (B::Λ))

theorem reduces_atomized {Φ Ξ Ω Ψ : List (NormalForm P)}
    (cutLeft : G P Φ (C::Ξ)) (root : G P (C::Ω) Ψ) :
    AtomizedReducesL cutLeft root (old p q f g) (p.chain q).keep := by
  intro hat a hr
  refine ⟨repair p q f g,?_,?_,denote p q f g,?_⟩
  · have hc:=hr.cutFree
    change (old p q f g).cutCount=0 at hc
    rw [old_count] at hc
    change (repair p q f g).cutCount=0
    rw [repair_count]
    exact hc
  · have hin : f.Atomized ∧ g.Atomized := by
      simpa only [old,ContractionSelection.performL_atomized,
        ContractionSelection.performR_atomized,G.Atomized] using hat
    simpa only [repair,middle,ContractionBlock.atomizedL,ContractionBlock.atomizedR,
      G.atomized_reindex,G.Atomized,ContractionSelection.performL_atomized,
      ContractionSelection.performR_atomized] using hin
  · intro I J v b y hv
    exact ReducibilityBoundary.descendants_left a (p.chain q).keep _ (blocked p q f g)
      (fun z hz => hr.entry_unique z hz) (endpoint_le p q f g) b y hv

end DosenPetric.Reduced.Gentzen.W5.ConjunctionAntecedent

namespace DosenPetric.Reduced.Gentzen.W5.OneDisjunctionSuccedent
universe u
variable {P : Type u} {A B C : NormalForm P} {F K U L Γ Θ : List (NormalForm P)}
section First
variable (p : ContractionSelection C F K) (f : G P (A::Γ) F) (g : G P (B::Θ) U)
theorem reducesFirst_atomized {Φ Ξ Ω Ψ : List (NormalForm P)} (hn : 2≤p.arity)
    (root : G P Φ (C::Ξ)) (cutRight : G P (C::Ω) Ψ) :
    AtomizedReducesR root cutRight (oldFirst p f g) (p.keep.before U) := by
  intro hat a hr
  refine ⟨repairFirst p f g,?_,?_,denoteFirst p f g,?_⟩
  · have hc:=hr.cutFree
    change (oldFirst p f g).cutCount=0 at hc
    rw [old_countFirst] at hc
    change (repairFirst p f g).cutCount=0
    rw [repair_countFirst]; exact hc
  · have hin : f.Atomized ∧ g.Atomized := by
      simpa only [oldFirst,ContractionSelection.performL_atomized,
        ContractionSelection.performR_atomized,G.Atomized] using hat
    simpa only [repairFirst,ContractionBlock.atomizedL,ContractionBlock.atomizedR,
      G.atomized_reindex,G.Atomized,ContractionSelection.performL_atomized,
      ContractionSelection.performR_atomized] using hin
  · intro I J v b y hv
    exact ReducibilityBoundary.strict_right a _ hr (endpoint_ltFirst p f g hn) b y hv
end First
section Second
variable (q : ContractionSelection C U L) (f : G P (A::Γ) F) (g : G P (B::Θ) U)
theorem reducesSecond_atomized {Φ Ξ Ω Ψ : List (NormalForm P)} (hn : 2≤q.arity)
    (root : G P Φ (C::Ξ)) (cutRight : G P (C::Ω) Ψ) :
    AtomizedReducesR root cutRight (oldSecond q f g) (At.shift F q.keep) := by
  intro hat a hr
  refine ⟨repairSecond q f g,?_,?_,denoteSecond q f g,?_⟩
  · have hc:=hr.cutFree
    change (oldSecond q f g).cutCount=0 at hc
    rw [old_countSecond] at hc
    change (repairSecond q f g).cutCount=0
    rw [repair_countSecond]; exact hc
  · have hin : f.Atomized ∧ g.Atomized := by
      simpa only [oldSecond,ContractionSelection.performL_atomized,
        ContractionSelection.performR_atomized,G.Atomized] using hat
    simpa only [repairSecond,ContractionBlock.atomizedL,ContractionBlock.atomizedR,
      G.atomized_reindex,G.Atomized,ContractionSelection.performL_atomized,
      ContractionSelection.performR_atomized] using hin
  · intro I J v b y hv
    exact ReducibilityBoundary.strict_right a _ hr (endpoint_ltSecond q f g hn) b y hv
end Second
end DosenPetric.Reduced.Gentzen.W5.OneDisjunctionSuccedent

namespace DosenPetric.Reduced.Gentzen.W5.DisjunctionSuccedent
universe u
variable {P : Type u} {A B C : NormalForm P} {F K U L Γ Θ : List (NormalForm P)}
variable (p : ContractionSelection C F K) (q : ContractionSelection C U L)
variable (f : G P (A::Γ) F) (g : G P (B::Θ) U)

theorem reduces_atomized {Φ Ξ Ω Ψ : List (NormalForm P)}
    (root : G P Φ (C::Ξ)) (cutRight : G P (C::Ω) Ψ) :
    AtomizedReducesR root cutRight (old p q f g) (p.chain q).keep := by
  intro hat a hr
  refine ⟨repair p q f g,?_,?_,denote p q f g,?_⟩
  · have hc:=hr.cutFree
    change (old p q f g).cutCount=0 at hc
    rw [old_count] at hc
    change (repair p q f g).cutCount=0
    rw [repair_count]; exact hc
  · have hin : f.Atomized ∧ g.Atomized := by
      simpa only [old,ContractionSelection.performL_atomized,
        ContractionSelection.performR_atomized,G.Atomized] using hat
    simpa only [repair,body,innerF,innerG,BlockedSource.headL,BlockedSource.disjLLast,BlockedSource.tailL,UnaryCast.exchangeL,ContractionBlock.atomizedL,ContractionBlock.atomizedR,
      G.atomized_reindex,G.Atomized,ContractionSelection.performL_atomized,
      ContractionSelection.performR_atomized] using hin
  · intro I J v b y hv
    obtain ⟨z,hz,ha⟩:=(a.replacement_cluster_iff (repair p q f g) b .right (.here C Ξ) y).mp hv.2.1.1
    have hx : z=(p.chain q).keep := hr.entry_unique z ha
    cases hx
    exact (repair_bound p q f g).bound b (p.chain q).keep rfl y hz hv.2.1.2 hv.2.2.1

end DosenPetric.Reduced.Gentzen.W5.DisjunctionSuccedent

namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u} {A B C : NormalForm P} {F K U L Γ Θ Φ Ξ Ω Λ : List (NormalForm P)}
namespace W5.OneDisjunctionAntecedent

theorem reducesFirst_atomized (p : ContractionSelection C F K) (hn : 2≤p.arity)
    (f : G P (A::F) Γ) (g : G P (B::U) Θ)
    (cutLeft : G P Φ (C::Ξ)) (root : G P (C::Ω) Λ) :
    AtomizedReducesL cutLeft root (oldFirst p f g) (.there (p.keep.before U)) := by
  intro hat a hr
  have he:=denoteFirst p f g
  refine ⟨repairFirst p f g,?_,?_,he,?_⟩
  · apply (repair_cutFreeFirst p f g).mpr
    have hc:=hr.cutFree
    change (oldFirst p f g).cutCount=0 at hc
    rw [old_countFirst] at hc
    exact Nat.add_eq_zero_iff.mp hc
  · have hin : f.Atomized ∧ g.Atomized := by
      simpa only [oldFirst,ContractionSelection.performL_atomized,
        ContractionSelection.performR_atomized,G.Atomized] using hat
    simpa only [repairFirst,ContractionBlock.atomizedL,ContractionBlock.atomizedR,
      G.atomized_reindex,G.Atomized,ContractionSelection.performL_atomized,
      ContractionSelection.performR_atomized] using hin
  · intro I J v b y hv
    exact ReducibilityBoundary.strict_left a _ hr (endpoint_ltFirst p f g hn) b y hv

theorem reducesSecond_atomized (q : ContractionSelection C U L) (hn : 2≤q.arity)
    (f : G P (A::F) Γ) (g : G P (B::U) Θ)
    (cutLeft : G P Φ (C::Ξ)) (root : G P (C::Ω) Λ) :
    AtomizedReducesL cutLeft root (oldSecond q f g) (.there (At.shift F q.keep)) := by
  intro hat a hr
  have he:=denoteSecond q f g
  refine ⟨repairSecond q f g,?_,?_,he,?_⟩
  · apply (repair_cutFreeSecond q f g).mpr
    have hc:=hr.cutFree
    change (oldSecond q f g).cutCount=0 at hc
    rw [old_countSecond] at hc
    exact Nat.add_eq_zero_iff.mp hc
  · have hin : f.Atomized ∧ g.Atomized := by
      simpa only [oldSecond,ContractionSelection.performL_atomized,
        ContractionSelection.performR_atomized,G.Atomized] using hat
    simpa only [repairSecond,ContractionBlock.atomizedL,ContractionBlock.atomizedR,
      G.atomized_reindex,G.Atomized,ContractionSelection.performL_atomized,
      ContractionSelection.performR_atomized] using hin
  · intro I J v b y hv
    exact ReducibilityBoundary.strict_left a _ hr (endpoint_ltSecond q f g hn) b y hv
end W5.OneDisjunctionAntecedent
end DosenPetric.Reduced.Gentzen

namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u} {A B C : NormalForm P} {F K U L Γ Θ Φ Ξ Ω Λ : List (NormalForm P)}
namespace W5.ParametricConjunction

theorem reduces_atomized (p : ContractionSelection C F K) (q : ContractionSelection C U L)
    (f : G P Γ (A::F)) (g : G P Θ (B::U))
    (root : G P Φ (C::Ξ)) (cutRight : G P (C::Ω) Λ) :
    AtomizedReducesR root cutRight (old p q f g) (.there (p.chain q).keep) := by
  intro hat a hr
  have he:=denote p q f g
  refine ⟨repair p q f g,?_,?_,he,?_⟩
  · apply (repair_cutFree p q f g).mpr
    have hc:=hr.cutFree
    change (old p q f g).cutCount=0 at hc
    rw [old_count] at hc
    exact Nat.add_eq_zero_iff.mp hc
  · have hin : f.Atomized ∧ g.Atomized := by
      simpa only [old,ContractionSelection.performL_atomized,
        ContractionSelection.performR_atomized,G.Atomized] using hat
    simpa only [repair,middle,ContractionBlock.atomizedL,ContractionBlock.atomizedR,
      G.atomized_reindex,G.Atomized,ContractionSelection.performL_atomized,
      ContractionSelection.performR_atomized] using hin
  · intro I J v b y hv
    exact ReducibilityBoundary.descendants_right a (.there (p.chain q).keep) _ (blocked p q f g)
      (fun z hz => hr.entry_unique z hz) (endpoint_le p q f g) b y hv
end W5.ParametricConjunction
namespace W5.OneConjunction

theorem reducesFirst_atomized (p : ContractionSelection C F K) (hn : 2≤p.arity)
    (f : G P Γ (A::F)) (g : G P Θ (B::U))
    (root : G P Φ (C::Ξ)) (cutRight : G P (C::Ω) Λ) :
    AtomizedReducesR root cutRight (oldFirst p f g) (.there (p.keep.before U)) := by
  intro hat a hr
  have he:=denoteFirst p f g
  refine ⟨repairFirst p f g,?_,?_,he,?_⟩
  · apply (repair_cutFreeFirst p f g).mpr
    have hc:=hr.cutFree
    change (oldFirst p f g).cutCount=0 at hc
    rw [old_countFirst] at hc
    exact Nat.add_eq_zero_iff.mp hc
  · have hin : f.Atomized ∧ g.Atomized := by
      simpa only [oldFirst,ContractionSelection.performL_atomized,
        ContractionSelection.performR_atomized,G.Atomized] using hat
    simpa only [repairFirst,ContractionBlock.atomizedL,ContractionBlock.atomizedR,
      G.atomized_reindex,G.Atomized,ContractionSelection.performL_atomized,
      ContractionSelection.performR_atomized] using hin
  · intro I J v b y hv
    exact ReducibilityBoundary.strict_right a _ hr (endpoint_ltFirst p f g hn) b y hv

theorem reducesSecond_atomized (q : ContractionSelection C U L) (hn : 2≤q.arity)
    (f : G P Γ (A::F)) (g : G P Θ (B::U))
    (root : G P Φ (C::Ξ)) (cutRight : G P (C::Ω) Λ) :
    AtomizedReducesR root cutRight (oldSecond q f g) (.there (At.shift F q.keep)) := by
  intro hat a hr
  have he:=denoteSecond q f g
  refine ⟨repairSecond q f g,?_,?_,he,?_⟩
  · apply (repair_cutFreeSecond q f g).mpr
    have hc:=hr.cutFree
    change (oldSecond q f g).cutCount=0 at hc
    rw [old_countSecond] at hc
    exact Nat.add_eq_zero_iff.mp hc
  · have hin : f.Atomized ∧ g.Atomized := by
      simpa only [oldSecond,ContractionSelection.performL_atomized,
        ContractionSelection.performR_atomized,G.Atomized] using hat
    simpa only [repairSecond,ContractionBlock.atomizedL,ContractionBlock.atomizedR,
      G.atomized_reindex,G.Atomized,ContractionSelection.performL_atomized,
      ContractionSelection.performR_atomized] using hin
  · intro I J v b y hv
    exact ReducibilityBoundary.strict_right a _ hr (endpoint_ltSecond q f g hn) b y hv
end W5.OneConjunction
end DosenPetric.Reduced.Gentzen

namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u} {A B : NormalForm P} {F K U L Γ Θ Φ Ξ Ω Λ : List (NormalForm P)}
namespace W6.OneHeadConjunction

theorem reducesFirst_atomized (p : ContractionSelection (.conj A B) F K)
    (f : G P Γ (A::F)) (g : G P Θ (B::U))
    (root : G P Φ (.conj A B::Ξ)) (cutRight : G P (.conj A B::Ω) Λ) :
    AtomizedReducesR root cutRight (oldFirst p f g) (p.keep.before U) := by
  intro hat a hr
  have he:=denoteFirst p f g
  refine ⟨repairFirst p f g,?_,?_,he,?_⟩
  · have hc:=hr.cutFree
    change (oldFirst p f g).cutCount=0 at hc
    rw [old_countFirst] at hc
    change (repairFirst p f g).cutCount=0
    rw [repair_countFirst]
    exact hc
  · have hin : f.Atomized ∧ g.Atomized := by
      simpa only [oldFirst,ContractionSelection.performL_atomized,
        ContractionSelection.performR_atomized,G.Atomized] using hat
    simpa only [repairFirst,middleFirst,ContractionBlock.atomizedL,ContractionBlock.atomizedR,
      G.atomized_reindex,G.Atomized,ContractionSelection.performL_atomized,
      ContractionSelection.performR_atomized] using hin
  · intro I J v b y hv
    exact ReducibilityBoundary.descendants_right a (p.keep.before U) _ (blockedFirst p f g)
      (fun z hz => hr.entry_unique z hz) (endpoint_leFirst p f g) b y hv

theorem reducesSecond_atomized (q : ContractionSelection (.conj A B) U L)
    (f : G P Γ (A::F)) (g : G P Θ (B::U))
    (root : G P Φ (.conj A B::Ξ)) (cutRight : G P (.conj A B::Ω) Λ) :
    AtomizedReducesR root cutRight (oldSecond q f g) (At.shift F q.keep) := by
  intro hat a hr
  have he:=denoteSecond q f g
  refine ⟨repairSecond q f g,?_,?_,he,?_⟩
  · have hc:=hr.cutFree
    change (oldSecond q f g).cutCount=0 at hc
    rw [old_countSecond] at hc
    change (repairSecond q f g).cutCount=0
    rw [repair_countSecond]
    exact hc
  · have hin : f.Atomized ∧ g.Atomized := by
      simpa only [oldSecond,ContractionSelection.performL_atomized,
        ContractionSelection.performR_atomized,G.Atomized] using hat
    simpa only [repairSecond,middleSecond,ContractionBlock.atomizedL,ContractionBlock.atomizedR,
      G.atomized_reindex,G.Atomized,ContractionSelection.performL_atomized,
      ContractionSelection.performR_atomized] using hin
  · intro I J v b y hv
    exact ReducibilityBoundary.descendants_right a (At.shift F q.keep) _ (blockedSecond q f g)
      (fun z hz => hr.entry_unique z hz) (endpoint_leSecond q f g) b y hv
end W6.OneHeadConjunction
namespace W6.HeadRight

theorem reduces_atomized (p : ContractionSelection (.conj A B) F K) (q : ContractionSelection (.conj A B) U L)
    (f : G P Γ (A::F)) (g : G P Θ (B::U))
    (root : G P Φ (.conj A B::Ξ)) (cutRight : G P (.conj A B::Ω) Λ) :
    AtomizedReducesR root cutRight (old p q f g) (p.chain q).keep := by
  intro hat a hr
  have h:=addressed_right p q f g a hr
  exact ⟨repair p q f g,h.1,(repair_atomized p q f g).mpr ((old_atomized p q f g).mp hat),h.2.1,h.2.2.2⟩
end W6.HeadRight
end DosenPetric.Reduced.Gentzen

namespace DosenPetric.Reduced.Gentzen.W6.OneHeadDisjunction
universe u
variable {P : Type u} {A B : NormalForm P} {F K U L Δ Λ : List (NormalForm P)}
section First
variable (p : ContractionSelection (.disj A B) F K) (f : G P (A::F) Δ) (g : G P (B::U) Λ)

theorem reducesFirst_atomized {Φ Ξ Ω Ψ : List (NormalForm P)}
    (cutLeft : G P Φ (.disj A B::Ξ)) (root : G P (.disj A B::Ω) Ψ) :
    AtomizedReducesL cutLeft root (oldFirst p f g) (p.keep.before U) := by
  intro hat a hr
  refine ⟨repairFirst p f g,?_,?_,denoteFirst p f g,?_⟩
  · have hc:=hr.cutFree
    change (oldFirst p f g).cutCount=0 at hc
    rw [old_countFirst] at hc
    change (repairFirst p f g).cutCount=0
    rw [repair_countFirst]; exact hc
  · have hin : f.Atomized ∧ g.Atomized := by
      simpa only [oldFirst,ContractionSelection.performL_atomized,
        ContractionSelection.performR_atomized,G.Atomized] using hat
    simpa only [repairFirst,bodyFirst,innerFirst,ContractionSelection.retainedReturn,UnaryCast.exchangeL,BlockedSource.disjLLast,BlockedSource.tailL,ContractionBlock.atomizedL,ContractionBlock.atomizedR,
      G.atomized_reindex,G.Atomized,ContractionSelection.performL_atomized,
      ContractionSelection.performR_atomized] using hin
  · intro I J v b y hv
    obtain ⟨z,hz,ha⟩:=(a.replacement_cluster_iff (repairFirst p f g) b .left (.here (.disj A B) Ω) y).mp hv.2.1.1
    have hx : z=p.keep.before U := hr.entry_unique z ha
    cases hx
    exact (repair_boundFirst p f g).bound b (p.keep.before U) rfl y hz hv.2.1.2 hv.2.2.1
end First
section Second
variable (q : ContractionSelection (.disj A B) U L) (f : G P (A::F) Δ) (g : G P (B::U) Λ)

theorem reducesSecond_atomized {Φ Ξ Ω Ψ : List (NormalForm P)}
    (cutLeft : G P Φ (.disj A B::Ξ)) (root : G P (.disj A B::Ω) Ψ) :
    AtomizedReducesL cutLeft root (oldSecond q f g) (At.shift F q.keep) := by
  intro hat a hr
  refine ⟨repairSecond q f g,?_,?_,denoteSecond q f g,?_⟩
  · have hc:=hr.cutFree
    change (oldSecond q f g).cutCount=0 at hc
    rw [old_countSecond] at hc
    change (repairSecond q f g).cutCount=0
    rw [repair_countSecond]; exact hc
  · have hin : f.Atomized ∧ g.Atomized := by
      simpa only [oldSecond,ContractionSelection.performL_atomized,
        ContractionSelection.performR_atomized,G.Atomized] using hat
    simpa only [repairSecond,bodySecond,innerSecond,ContractionSelection.retainedReturn,UnaryCast.exchangeL,BlockedSource.disjLLast,BlockedSource.tailL,ContractionBlock.atomizedL,ContractionBlock.atomizedR,
      G.atomized_reindex,G.Atomized,ContractionSelection.performL_atomized,
      ContractionSelection.performR_atomized] using hin
  · intro I J v b y hv
    obtain ⟨z,hz,ha⟩:=(a.replacement_cluster_iff (repairSecond q f g) b .left (.here (.disj A B) Ω) y).mp hv.2.1.1
    have hx : z=At.shift F q.keep := hr.entry_unique z ha
    cases hx
    exact (repair_boundSecond q f g).bound b (At.shift F q.keep) rfl y hz hv.2.1.2 hv.2.2.1
end Second
end DosenPetric.Reduced.Gentzen.W6.OneHeadDisjunction

namespace DosenPetric.Reduced.Gentzen.W5.ParametricDisjunction
universe u
variable {P : Type u} {A B C : NormalForm P} {F K U L Δ Λ : List (NormalForm P)}
variable (p : ContractionSelection C F K) (q : ContractionSelection C U L)
variable (f : G P (A::F) Δ) (g : G P (B::U) Λ)

theorem reduces_atomized {Φ Ξ Ω Ψ : List (NormalForm P)}
    (cutLeft : G P Φ (C::Ξ)) (root : G P (C::Ω) Ψ) :
    AtomizedReducesL cutLeft root (old p q f g) (.there (p.chain q).keep) := by
  intro hat a hr
  refine ⟨repair p q f g,?_,?_,denote p q f g,?_⟩
  · have hc:=hr.cutFree
    change (old p q f g).cutCount=0 at hc
    rw [old_count] at hc
    change (repair p q f g).cutCount=0
    rw [repair_count]; exact hc
  · have hin : f.Atomized ∧ g.Atomized := by
      simpa only [old,ContractionSelection.performL_atomized,
        ContractionSelection.performR_atomized,G.Atomized] using hat
    simpa only [repair,body,innerF,innerG,BlockedSource.headL,BlockedSource.disjLLast,BlockedSource.tailL,UnaryCast.exchangeL,ContractionBlock.atomizedL,ContractionBlock.atomizedR,
      G.atomized_reindex,G.Atomized,ContractionSelection.performL_atomized,
      ContractionSelection.performR_atomized] using hin
  · intro I J v b y hv
    obtain ⟨z,hz,ha⟩:=(a.replacement_cluster_iff (repair p q f g) b .left (.here C Ω) y).mp hv.2.1.1
    have hx : z=.there (p.chain q).keep := hr.entry_unique z ha
    cases hx
    exact (repair_bound p q f g).bound b (.there (p.chain q).keep) rfl y hz hv.2.1.2 hv.2.2.1
end DosenPetric.Reduced.Gentzen.W5.ParametricDisjunction

namespace DosenPetric.Reduced.Gentzen.W6.TerminalOne
universe u
variable {P : Type u} {A B : NormalForm P} {F K U L Δ Λ : List (NormalForm P)}
section First
variable (p : ContractionSelection (.disj A B) F K) (f : G P (F++[A]) Δ) (g : G P (U++[B]) Λ)

theorem reducesFirst_atomized {Φ Ξ Ω Ψ : List (NormalForm P)}
    (cutLeft : G P Φ (.disj A B::Ξ)) (root : G P (.disj A B::Ω) Ψ) :
    AtomizedReducesL cutLeft root (oldFirst p f g) (p.extend U).lastKeep := by
  intro hat a hr
  have h:=addressedFirst p f g a hr
  exact ⟨repairFirst p f g,h.1,(repair_atomizedFirst p f g).mpr ((old_atomizedFirst p f g).mp hat),h.2.1,h.2.2.2⟩
end First
section Second
variable (q : ContractionSelection (.disj A B) U L) (f : G P (F++[A]) Δ) (g : G P (U++[B]) Λ)

theorem reducesSecond_atomized {Φ Ξ Ω Ψ : List (NormalForm P)}
    (cutLeft : G P Φ (.disj A B::Ξ)) (root : G P (.disj A B::Ω) Ψ) :
    AtomizedReducesL cutLeft root (oldSecond q f g) (q.prependFixed F).lastKeep := by
  intro hat a hr
  have h:=addressedSecond q f g a hr
  exact ⟨repairSecond q f g,h.1,(repair_atomizedSecond q f g).mpr ((old_atomizedSecond q f g).mp hat),h.2.1,h.2.2.2⟩
end Second
end DosenPetric.Reduced.Gentzen.W6.TerminalOne

namespace DosenPetric.Reduced.Gentzen.W6.SourceLeft
universe u
variable {P : Type u} {A B : NormalForm P} {F K U L Δ Λ Φ Ξ Ω Ψ : List (NormalForm P)}

theorem reduces_atomized (p : ContractionSelection (.disj A B) F K)
    (q : ContractionSelection (.disj A B) U L)
    (f : G P (F++[A]) Δ) (g : G P (U++[B]) Λ)
    (cutLeft : G P Φ (.disj A B::Ξ)) (root : G P (.disj A B::Ω) Ψ) :
    AtomizedReducesL cutLeft root (old p q f g) (p.sourceKeep q) := by
  intro hat a hr
  have h := addressed_left p q f g a hr
  exact ⟨repair p q f g,h.1,(repair_atomized p q f g).mpr ((old_atomized p q f g).mp hat),
    h.2.1,h.2.2.2⟩
end DosenPetric.Reduced.Gentzen.W6.SourceLeft
