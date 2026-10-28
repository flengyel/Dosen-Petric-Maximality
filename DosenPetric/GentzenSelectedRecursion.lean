module

public import DosenPetric.GentzenSelectedBlocked

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

namespace PositionalCut
variable {Γ Δ Θ Λ : List (NormalForm P)} {C : NormalForm P}

theorem rank_left_predecessor (f : G P Γ Δ) (x : At Δ C)
    (g : G P Θ Λ) (y : At Θ C) (a : Upper f .right C)
    (ha : f.IsPredecessor .right x a) :
    rank a.branch.proof a.position g y < rank f x g y := by
  have hh := f.rho_child_lt .right x a ha
  unfold rank
  omega

theorem rank_right_predecessor (f : G P Γ Δ) (x : At Δ C)
    (g : G P Θ Λ) (y : At Θ C) (a : Upper g .left C)
    (ha : g.IsPredecessor .left y a) :
    rank f x a.branch.proof a.position < rank f x g y := by
  have hh := g.rho_child_lt .left y a ha
  unfold rank
  omega

theorem clean_left_predecessor {f : G P Γ Δ} {x : At Δ C}
    {g : G P Θ Λ} {y : At Θ C} (h : Clean f x g y)
    (a : Upper f .right C) (ha : f.IsPredecessor .right x a) :
    Clean a.branch.proof a.position g y := by
  refine ⟨a.branch.occurrence.cutFree h.1, h.2.1,
    a.branch.occurrence.atomized h.2.2.1, h.2.2.2.1, ?_, h.2.2.2.2.2⟩
  apply AllBlockedAt.inherit h.2.2.2.2.1 (ProofAddress.root.down a.branch.occurrence) a.position
  change (a.branch.occurrence.parent .right a.position).bind (fun z => some z) = some x
  change a.branch.occurrence.parent .right a.position = some x at ha
  rw [ha]
  rfl

theorem clean_right_predecessor {f : G P Γ Δ} {x : At Δ C}
    {g : G P Θ Λ} {y : At Θ C} (h : Clean f x g y)
    (a : Upper g .left C) (ha : g.IsPredecessor .left y a) :
    Clean f x a.branch.proof a.position := by
  refine ⟨h.1, a.branch.occurrence.cutFree h.2.1,
    h.2.2.1, a.branch.occurrence.atomized h.2.2.2.1, h.2.2.2.2.1, ?_⟩
  apply AllBlockedAt.inherit h.2.2.2.2.2 (ProofAddress.root.down a.branch.occurrence) a.position
  change (a.branch.occurrence.parent .left a.position).bind (fun z => some z) = some y
  change a.branch.occurrence.parent .left a.position = some y at ha
  rw [ha]
  rfl

end PositionalCut
end DosenPetric.Reduced.Gentzen
