module

public import DosenPetric.GentzenRetainedLastBounds

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.W6.OneHeadDisjunction
universe u
variable {P : Type u} {A B : NormalForm P} {F K U L Δ Λ : List (NormalForm P)}
section First
variable (p : ContractionSelection (.disj A B) F K) (f : G P (A::F) Δ) (g : G P (B::U) Λ)

theorem body_boundFirst : ContractionBound .left (.disj A B) (limitFirst p f g) (bodyFirst p f g)
    (fun x=>x.index=(p.extend U).lastKeep.index) := by
  unfold bodyFirst
  apply (p.extend U).retainedLastBlock.left_bound (p.extend U).retainedLast_bound _ _
    (fun i=>i=(p.extend U).lastKeep.index) (blockedFirst p f g)
  apply BlockedSource.native_source_bound _ _
    (fun i=>copyIndex (p.extend U).retainedLastBlock.gs i=(p.extend U).lastKeep.index)
  · apply ContractionBound.bounded
    intro x hx
    change At (A::K) (.disj A B) at x
    change 0<x.index ∧ copyIndex (p.extend U).retainedLastBlock.gs
      (exchangeIndex 0 1 (K++U).length x.index)=(p.extend U).lastKeep.index at hx
    have h₀ : 0<x.index := hx.1
    have hi:=x.index_lt
    simp only [List.length_cons] at hi
    rw [EntryFrame.exchange_head_index _ x.index h₀ (by simp only [List.length_append]; omega)] at hx
    have hm:=((p.extend U).last_selected_index _).mp hx.2
    rw [p.extend_keep,At.index_before] at hm
    simp only [List.length_append] at hm
    have hp : p.keep.index<K.length := p.keep.index_lt
    have he : x=.there p.keep := At.index_injective _ _ (by simp only [At.index]; omega)
    subst x
    exact inner_ltFirst p f g
  · apply ContractionBound.bounded
    intro x hx
    change At (B::U) (.disj A B) at x
    change 0<x.index ∧ copyIndex (p.extend U).retainedLastBlock.gs
      (exchangeIndex 0 1 (K++U).length (K.length+x.index))=(p.extend U).lastKeep.index at hx
    have h₀ : 0<x.index := hx.1
    have hi:=x.index_lt
    simp only [List.length_cons] at hi
    rw [EntryFrame.exchange_head_index _ (K.length+x.index) (by omega) (by simp only [List.length_append]; omega)] at hx
    have hm:=((p.extend U).last_selected_index _).mp hx.2
    rw [p.extend_keep,At.index_before] at hm
    simp only [List.length_append] at hm
    have hp : p.keep.index<K.length := p.keep.index_lt
    omega

theorem repair_boundFirst : ContractionBound .left (.disj A B) (limitFirst p f g) (repairFirst p f g)
    (fun x=>x.index=(p.keep.before U).index) := by
  have h:=(p.extend U).return_bound (bodyFirst p f g) (body_boundFirst p f g)
  rw [p.extend_keep] at h
  exact h

theorem reducesFirst {Φ Ξ Ω Ψ : List (NormalForm P)}
    (cutLeft : G P Φ (.disj A B::Ξ)) (root : G P (.disj A B::Ω) Ψ) :
    ReducesL cutLeft root (oldFirst p f g) (p.keep.before U) := by
  intro a hr
  refine ⟨repairFirst p f g,?_,denoteFirst p f g,?_⟩
  · have hc:=hr.cutFree
    change (oldFirst p f g).cutCount=0 at hc
    rw [old_countFirst] at hc
    change (repairFirst p f g).cutCount=0
    rw [repair_countFirst]; exact hc
  · intro I J v b y hv
    obtain ⟨z,hz,ha⟩:=(a.replacement_cluster_iff (repairFirst p f g) b .left (.here (.disj A B) Ω) y).mp hv.2.1.1
    have hx : z=p.keep.before U := hr.entry_unique z ha
    cases hx
    exact (repair_boundFirst p f g).bound b (p.keep.before U) rfl y hz hv.2.1.2 hv.2.2.1
end First
section Second
variable (q : ContractionSelection (.disj A B) U L) (f : G P (A::F) Δ) (g : G P (B::U) Λ)

theorem body_boundSecond : ContractionBound .left (.disj A B) (limitSecond q f g) (bodySecond q f g)
    (fun x=>x.index=(q.prependFixed F).lastKeep.index) := by
  unfold bodySecond
  apply (q.prependFixed F).retainedLastBlock.left_bound (q.prependFixed F).retainedLast_bound _ _
    (fun i=>i=(q.prependFixed F).lastKeep.index) (blockedSecond q f g)
  apply BlockedSource.native_source_bound _ _
    (fun i=>copyIndex (q.prependFixed F).retainedLastBlock.gs i=(q.prependFixed F).lastKeep.index)
  · apply ContractionBound.bounded
    intro x hx
    change At (A::F) (.disj A B) at x
    change 0<x.index ∧ copyIndex (q.prependFixed F).retainedLastBlock.gs
      (exchangeIndex 0 1 (F++L).length x.index)=(q.prependFixed F).lastKeep.index at hx
    have h₀ : 0<x.index := hx.1
    have hi:=x.index_lt
    simp only [List.length_cons] at hi
    rw [EntryFrame.exchange_head_index _ x.index h₀ (by simp only [List.length_append]; omega)] at hx
    have hm:=((q.prependFixed F).last_selected_index _).mp hx.2
    rw [q.prepend_keep,At.index_shift] at hm
    simp only [List.length_append] at hm
    omega
  · apply ContractionBound.bounded
    intro x hx
    change At (B::L) (.disj A B) at x
    change 0<x.index ∧ copyIndex (q.prependFixed F).retainedLastBlock.gs
      (exchangeIndex 0 1 (F++L).length (F.length+x.index))=(q.prependFixed F).lastKeep.index at hx
    have h₀ : 0<x.index := hx.1
    have hi:=x.index_lt
    simp only [List.length_cons] at hi
    rw [EntryFrame.exchange_head_index _ (F.length+x.index) (by omega) (by simp only [List.length_append]; omega)] at hx
    have hm:=((q.prependFixed F).last_selected_index _).mp hx.2
    rw [q.prepend_keep,At.index_shift] at hm
    simp only [List.length_append] at hm
    have he : x=.there q.keep := At.index_injective _ _ (by simp only [At.index]; omega)
    subst x
    exact inner_ltSecond q f g

theorem repair_boundSecond : ContractionBound .left (.disj A B) (limitSecond q f g) (repairSecond q f g)
    (fun x=>x.index=(At.shift F q.keep).index) := by
  have h:=(q.prependFixed F).return_bound (bodySecond q f g) (body_boundSecond q f g)
  rw [q.prepend_keep] at h
  exact h

theorem reducesSecond {Φ Ξ Ω Ψ : List (NormalForm P)}
    (cutLeft : G P Φ (.disj A B::Ξ)) (root : G P (.disj A B::Ω) Ψ) :
    ReducesL cutLeft root (oldSecond q f g) (At.shift F q.keep) := by
  intro a hr
  refine ⟨repairSecond q f g,?_,denoteSecond q f g,?_⟩
  · have hc:=hr.cutFree
    change (oldSecond q f g).cutCount=0 at hc
    rw [old_countSecond] at hc
    change (repairSecond q f g).cutCount=0
    rw [repair_countSecond]; exact hc
  · intro I J v b y hv
    obtain ⟨z,hz,ha⟩:=(a.replacement_cluster_iff (repairSecond q f g) b .left (.here (.disj A B) Ω) y).mp hv.2.1.1
    have hx : z=At.shift F q.keep := hr.entry_unique z ha
    cases hx
    exact (repair_boundSecond q f g).bound b (At.shift F q.keep) rfl y hz hv.2.1.2 hv.2.2.1
end Second
end DosenPetric.Reduced.Gentzen.W6.OneHeadDisjunction
