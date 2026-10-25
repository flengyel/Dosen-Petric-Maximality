module

public import DosenPetric.GentzenReducibilitySourceLogical

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.ContractionSelection
universe u
variable {P : Type u} {C : NormalForm P} {F K : List (NormalForm P)}

theorem singleton_rest (p : ContractionSelection C F K) (h : p.arity=1) : p.rest=[] := by
  have hc:=p.count
  change (p.first::p.rest).length=p.arity at hc
  rw [h] at hc
  exact List.eq_nil_iff_length_eq_zero.mpr (by simp only [List.length_cons] at hc; omega)

theorem singleton_performL (p : ContractionSelection C F K) (h : p.arity=1)
    {Δ : List (NormalForm P)} (f : G P F Δ) :
    p.performL Δ f=f.reindex (p.singleton_endpoints h) rfl := by
  unfold performL
  rw [dite_eq_right (by omega : ¬2≤p.arity)]

theorem source_eq_retained_singletons {U : List (NormalForm P)}
    (p : ContractionSelection C F F) (q : ContractionSelection C U U)
    (hp : p.arity=1) (hq : q.arity=1) : p.sourceOld q=p.sourceRetained q := by
  apply eq_of_gs
  rw [sourceOld,gs_cast,chain_gs,chain_first,chain_rest,
    sourceRetained_gs]
  simp only [gs,p.singleton_rest hp,q.singleton_rest hq,gaps,List.append_nil,first,rest,List.nil_append,List.cons_append]

end DosenPetric.Reduced.Gentzen.ContractionSelection

namespace DosenPetric.Reduced.Gentzen.W6.SourceLeft
universe u
variable {P : Type u} {A B : NormalForm P} {F K U L Δ Λ : List (NormalForm P)}

theorem old_singletons_blocked
    (p : ContractionSelection (.disj A B) F K) (q : ContractionSelection (.disj A B) U L)
    (hp : p.arity=1) (hq : q.arity=1)
    (f : G P (F++[A]) Δ) (g : G P (U++[B]) Λ) : BlockedL (old p q f g) := by
  cases p.singleton_endpoints hp
  cases q.singleton_endpoints hq
  have hi : (p.extend [A]).performL Δ f=f :=
    ContractionSelection.singleton_performL _ (by rw [p.extend_arity]; exact hp) f
  have hj : (q.extend [B]).performL Λ g=g :=
    ContractionSelection.singleton_performL _ (by rw [q.extend_arity]; exact hq) g
  have hm : middle p q f g=BlockedSource.disjLLast f g := by rw [middle,hi,hj]
  have he : repair p q f g=old p q f g := by
    rw [repair,hm,←ContractionSelection.source_eq_retained_singletons p q hp hq]
    rfl
  rw [←he]
  exact repair_blocked p q f g

end DosenPetric.Reduced.Gentzen.W6.SourceLeft
