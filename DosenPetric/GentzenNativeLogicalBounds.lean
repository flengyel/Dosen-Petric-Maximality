module

public import DosenPetric.GentzenNativeLogicalBoundCoordinates
public import DosenPetric.GentzenLeftContractionBounds

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.W6.NativeLeft
universe u
variable {P : Type u} {A B : NormalForm P} {F K U L Δ Λ : List (NormalForm P)}
variable (p : ContractionSelection (.disj A B) F K) (q : ContractionSelection (.disj A B) U L)
variable (f : G P (A::F) Δ) (g : G P (B::U) Λ)

def limit : Nat := (old p q f g).rho .left (p.chain q).keep

theorem innerF_bound : ContractionBound .left (.disj A B) (limit p q f g) (innerF p f)
    (fun a => a.index=p.keep.index+1) := by
  apply ContractionBound.bounded
  intro a ha
  change At (A::K) (.disj A B) at a
  have he : a=.there p.keep := At.index_injective _ _ ha
  subst a
  exact innerF_lt p q f g

theorem innerG_bound : ContractionBound .left (.disj A B) (limit p q f g) (innerG q g)
    (fun a => a.index=q.keep.index+1) := by
  apply ContractionBound.bounded
  intro a ha
  change At (B::L) (.disj A B) at a
  have he : a=.there q.keep := At.index_injective _ _ ha
  subst a
  exact innerG_lt p q f g

theorem body_bound : ContractionBound .left (.disj A B) (limit p q f g) (body p q f g)
    (fun a => a.index=(p.sourceKeep q).index) := by
  unfold body
  apply (W6.SourceLeft.tripleBlock p q).left_bound (W6.SourceLeft.triple_bound p q) _ _
    (fun i => i=(p.sourceKeep q).index) (body_blocked p q f g)
  apply BlockedSource.native_source_bound _ _
    (fun i => copyIndex (W6.SourceLeft.tripleBlock p q).gs i=(p.sourceKeep q).index)
  · apply (innerF_bound p q f g).mono
    intro a ha
    change At (A::K) (.disj A B) at a
    change 0<a.index ∧ copyIndex (W6.SourceLeft.tripleBlock p q).gs
      (exchangeIndex 0 1 (K++L).length a.index)=(p.sourceKeep q).index at ha
    have ha0 : 0<a.index := ha.1
    have hi:=a.index_lt
    simp only [List.length_cons] at hi
    have hm:=(triple_selected_index p q _).mp ha.2
    rw [EntryFrame.exchange_head_index _ a.index ha.1 (by simp only [List.length_append]; omega)] at hm
    rw [p.keep_index]
    exact first_branch_index a.index K.length L.length (gaps p.gs).length p.tail.length (gaps q.gs).length
      ha0 hi p.lower_length hm
  · apply (innerG_bound p q f g).mono
    intro a ha
    change At (B::L) (.disj A B) at a
    change 0<a.index ∧ copyIndex (W6.SourceLeft.tripleBlock p q).gs
      (exchangeIndex 0 1 (K++L).length (K.length+a.index))=(p.sourceKeep q).index at ha
    have ha0 : 0<a.index := ha.1
    have hi:=a.index_lt
    simp only [List.length_cons] at hi
    have hm:=(triple_selected_index p q _).mp ha.2
    rw [EntryFrame.exchange_head_index _ (K.length+a.index) (by omega)
      (by simp only [List.length_append]; omega)] at hm
    rw [q.keep_index]
    exact second_branch_index a.index K.length L.length (gaps p.gs).length p.tail.length
      (gaps q.gs).length q.tail.length ha0 hi p.lower_length q.lower_length hm

theorem repair_bound : ContractionBound .left (.disj A B) (limit p q f g) (repair p q f g)
    (fun a => a.index=(p.chain q).keep.index) := by
  unfold repair
  apply UnaryCast.exchangeL_bound (base p q) q.tail [.disj A B] [] (exit_source p q) (exit_target p q)
    (Δ++Λ) (body p q f g) (fun i => i=(p.chain q).keep.index)
  apply (body_bound p q f g).mono
  intro a ha
  change exchangeIndex (base p q).length q.tail.length 1 a.index=(p.chain q).keep.index at ha
  have hk:=congrArg At.index (exit_retained p q)
  rw [exit_index] at hk
  exact exit_index_injective p q _ _ (ha.trans hk.symm)

end DosenPetric.Reduced.Gentzen.W6.NativeLeft
