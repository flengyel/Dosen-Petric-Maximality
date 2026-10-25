module

public import DosenPetric.GentzenSelectionExtension

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.ContractionSelection
universe u
variable {P : Type u} {C : NormalForm P}

theorem blockArity {F K : List (NormalForm P)} (p : ContractionSelection C F K)
    (hn : 2 ≤ p.arity) : 2 ≤ p.block.gs.length := by
  change 2 ≤ p.gs.length
  rw [p.count]
  exact hn

/-- Joint positional extraction from two adjacent premise contexts. The index
    identifies both the actual lower context and the original selection. -/
inductive Split (C : NormalForm P) (F U : List (NormalForm P)) :
    {K : List (NormalForm P)} → ContractionSelection C (F++U) K → Type u where
  | left {K} (p : ContractionSelection C F K) : Split C F U (p.extend U)
  | right {L} (q : ContractionSelection C U L) : Split C F U (q.prependFixed F)
  | both {K L} (p : ContractionSelection C F K) (q : ContractionSelection C U L) :
      Split C F U (p.chain q)

theorem split_exists (F U : List (NormalForm P)) {K : List (NormalForm P)}
    (p : ContractionSelection C (F++U) K) : Nonempty (Split C F U p) := by
  induction F generalizing K with
  | nil => exact ⟨.right p⟩
  | cons A F ih =>
    cases p with
    | last Θ => exact ⟨.left (.last F)⟩
    | fixed A p =>
      obtain ⟨h⟩ := ih p
      cases h with
      | left q => exact ⟨.left (.fixed A q)⟩
      | right q => exact ⟨.right q⟩
      | both p q => exact ⟨.both (.fixed A p) q⟩
    | more p =>
      obtain ⟨h⟩ := ih p
      cases h with
      | left q => exact ⟨.left (.more q)⟩
      | right q => exact ⟨.both (.last F) q⟩
      | both p q => exact ⟨.both (.more p) q⟩

theorem prepend_arity {F K : List (NormalForm P)} (p : ContractionSelection C F K)
    (Ξ : List (NormalForm P)) : (p.prependFixed Ξ).arity=p.arity :=
  (p.prependFixed Ξ).count.symm.trans ((p.prepend_count Ξ).trans p.count)

theorem prepend_block {F K : List (NormalForm P)} (p : ContractionSelection C F K)
    (hn : 2 ≤ p.arity) (Ξ : List (NormalForm P)) :
    (p.prependFixed Ξ).block = p.block.prepend (by rw [p.count]; exact hn) Ξ := by
  have hs : p.block.selection (p.block.nonempty (by rw [p.count]; exact hn))=p := by
    apply ext_selected
    exact (p.block.selection_selected (by rw [p.count]; exact hn)).trans p.selected_eq.symm
  unfold ContractionBlock.prepend
  rw [hs]

end DosenPetric.Reduced.Gentzen.ContractionSelection
