module

public import DosenPetric.GentzenSelectedRecursion

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

/-- Root and immediate-predecessor characterization of selected blockedness. -/
theorem allBlockedAt_iff_branches {Γ Δ : List (NormalForm P)} (g : G P Γ Δ)
    (s : SequentSide) {C : NormalForm P} (x : Place s Γ Δ C) :
    AllBlockedAt g s x ↔
      (G.LowerContraction g s x → BlockedOn s g) ∧
      ∀ a : Upper g s C, g.IsPredecessor s x a →
        AllBlockedAt a.branch.proof s a.position := by
  constructor
  · intro h
    refine ⟨fun hl => h ProofAddress.root x rfl hl, ?_⟩
    intro a ha
    apply AllBlockedAt.inherit h (ProofAddress.root.down a.branch.occurrence) a.position
    change (a.branch.occurrence.parent s a.position).bind (fun z => some z) = some x
    change a.branch.occurrence.parent s a.position = some x at ha
    rw [ha]
    rfl
  · intro h U V w a z hz hl
    have hsp : ∀ (b : ProofSpine g w), b.toAddress.ascend s z = some x → BlockedOn s w := by
      intro b hb
      cases b with
      | root =>
        have he : z = x := Option.some.inj hb
        cases he
        exact h.1 hl
      | @down _ _ K L _ _ _ v _ p b =>
        rw [ProofSpine.toAddress, ProofAddress.ascend_append] at hb
        cases hq : b.toAddress.ascend s z with
        | none => simp only [hq, Option.bind_none] at hb; cases hb
        | some q =>
          have hp : p.parent s q = some x := by
            cases hp : p.parent s q <;> simp_all [ProofAddress.ascend]
          exact h.2 ⟨⟨K,L,v,p⟩,q⟩ hp b.toAddress z hq hl
    exact hsp a.spine (by simpa only [ProofAddress.spine_toAddress] using hz)

end DosenPetric.Reduced.Gentzen
