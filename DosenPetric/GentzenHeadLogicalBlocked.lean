module

public import DosenPetric.GentzenHeadLogicalContraction
public import DosenPetric.GentzenMixSelectionReducer

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

theorem G.conjR_reindex_inputs {Γ Θ Δ Λ Δ' Λ' : List (NormalForm P)} {A B : NormalForm P}
    (f : G P Γ (A::Δ)) (g : G P Θ (B::Λ)) (hΔ : Δ=Δ') (hΛ : Λ=Λ') :
    G.conjR (f.reindex rfl (congrArg (List.cons A) hΔ)) (g.reindex rfl (congrArg (List.cons B) hΛ)) =
      (G.conjR f g).reindex rfl (by cases hΔ; cases hΛ; rfl) := by
  cases hΔ; cases hΛ; rfl

namespace W6.HeadRight
variable {A B : NormalForm P} {F K U L Γ Θ : List (NormalForm P)}
variable (p : ContractionSelection (.conj A B) F K) (q : ContractionSelection (.conj A B) U L)
variable (f : G P Γ (A::F)) (g : G P Θ (B::U))

theorem repair_blocked : BlockedR (repair p q f g) := by
  have h:=BlockedR.conjunctionBoth A B Γ Θ (gaps p.gs) p.tail (gaps q.gs) q.tail
    (((p.prependFixed [A]).performR Γ f).reindex rfl (congrArg (List.cons A) p.lower.symm))
    (((q.prependFixed [B]).performR Θ g).reindex rfl (congrArg (List.cons B) q.lower.symm))
  have hm:=G.conjR_reindex_inputs ((p.prependFixed [A]).performR Γ f)
    ((q.prependFixed [B]).performR Θ g) p.lower.symm q.lower.symm
  have he:=h.reindex rfl (p.mergeBlock q).lower
  unfold BlockedSource.right3 at he
  rw [hm] at he
  simpa only [repair,ContractionBlock.applyR,ContractionBlock.selectedHead,
    ContractionSelection.mergeBlock,G.reindex_trans,middle] using he

theorem old_count : (old p q f g).cutCount=f.cutCount+g.cutCount := by
  rw [old,ContractionSelection.performR_count]; rfl
theorem repair_count : (repair p q f g).cutCount=f.cutCount+g.cutCount := by
  rw [repair,ContractionBlock.countR]
  simp only [middle,G.cutCount,ContractionSelection.performR_count]
theorem old_cutFree : (old p q f g).CutFree ↔ f.CutFree ∧ g.CutFree := by
  simp only [G.CutFree,old_count,Nat.add_eq_zero_iff]
theorem repair_cutFree : (repair p q f g).CutFree ↔ f.CutFree ∧ g.CutFree := by
  simp only [G.CutFree,repair_count,Nat.add_eq_zero_iff]
theorem old_atomized : (old p q f g).Atomized ↔ f.Atomized ∧ g.Atomized := by
  simp only [old,ContractionSelection.performR_atomized,G.Atomized]
theorem repair_atomized : (repair p q f g).Atomized ↔ f.Atomized ∧ g.Atomized := by
  simp only [repair,middle,ContractionBlock.atomizedR,G.Atomized,ContractionSelection.performR_atomized]
theorem relation : (repair p q f g).relation=(old p q f g).relation := congrArg occurrenceMap (denote p q f g)

end W6.HeadRight
end DosenPetric.Reduced.Gentzen
