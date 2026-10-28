module

public import DosenPetric.GentzenSameSideLogicalHeads

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace SameSideLogical

/-- Rebuild conjunction-left after deleting a selected prefix occurrence. -/
def conjBefore {Γ F U Λ D : List (NormalForm P)} {A B C : NormalForm P}
    (a : At F C) (f : G P ((a.before (A :: B :: U)).erase ++ Γ) (Λ ++ D)) :
    G P ((a.before (.conj A B :: U)).erase ++ Γ) (Λ ++ D) :=
  (SuffixedLogical.conjL a.erase U Γ (Λ ++ D) A B
    (f.reindex (congrArg (fun xs => xs ++ Γ) (a.erase_before (A :: B :: U))) rfl)).reindex
      (congrArg (fun xs => xs ++ Γ) (a.erase_before (.conj A B :: U))).symm rfl

/-- Rebuild disjunction-right after deleting a selected prefix occurrence. -/
def disjBefore {I F U Λ : List (NormalForm P)} {A B C : NormalForm P}
    (a : At F C) (f : G P I (Λ ++ (a.before (A :: B :: U)).erase)) :
    G P I (Λ ++ (a.before (.disj A B :: U)).erase) :=
  (PrefixedLogical.disjR I Λ a.erase U A B
    (f.reindex rfl (congrArg (fun xs => Λ ++ xs) (a.erase_before (A :: B :: U))))).reindex
      rfl (congrArg (fun xs => Λ ++ xs) (a.erase_before (.disj A B :: U))).symm

end SameSideLogical
namespace CutCommutation

/-- Exact positional conjunction-left prefix commutation, including residual list transports. -/
theorem same_conjL_before {Γ Δ F U Λ : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P Γ Δ) (x : At Δ C) (g : G P (F ++ A :: B :: U) Λ) (a : At F C) :
    ofTerm (PositionalCut.cut f x (G.conjL F U Λ A B g) (a.before (.conj A B :: U))).denote =
      ofTerm (SameSideLogical.conjBefore a
        (PositionalCut.cut f x g (a.before (A :: B :: U)))).denote := by
  apply G.reindex_left_cancel_denote
    (congrArg (fun xs => xs ++ Γ) (a.erase_before (.conj A B :: U)))
  rw [PositionalCut.reindex_residues f x _ _ rfl (a.erase_before (.conj A B :: U))]
  change ofTerm (G.cut (x.toHead.right f)
    ((LogicalDeletion.headBefore a (.conj A B :: U)).left (G.conjL F U Λ A B g))).denote = _
  rw [PositionalCut.reindex_residues f x g _ rfl (a.erase_before (A :: B :: U))]
  exact same_conjL_head (x.toHead.right f) g _ _
    (LogicalDeletion.before_square .conj U A B a)

/-- Exact positional disjunction-right prefix commutation at the original selected tag. -/
theorem same_disjR_before {Γ F U Θ Λ : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P Γ (F ++ A :: B :: U)) (a : At F C) (g : G P Θ Λ) (y : At Θ C) :
    ofTerm (PositionalCut.cut (G.disjR Γ F U A B f) (a.before (.disj A B :: U)) g y).denote =
      ofTerm (SameSideLogical.disjBefore a
        (PositionalCut.cut f (a.before (A :: B :: U)) g y)).denote := by
  apply G.reindex_right_cancel_denote
    (congrArg (fun xs => Λ ++ xs) (a.erase_before (.disj A B :: U)))
  rw [PositionalCut.reindex_residues _ _ g y (a.erase_before (.disj A B :: U)) rfl]
  change ofTerm (G.cut ((LogicalDeletion.headBefore a (.disj A B :: U)).right
    (G.disjR Γ F U A B f)) (y.toHead.left g)).denote = _
  rw [PositionalCut.reindex_residues f _ g y (a.erase_before (A :: B :: U)) rfl]
  exact same_disjR_head f (y.toHead.left g) _ _
    (LogicalDeletion.before_square .disj U A B a)

end CutCommutation
end DosenPetric.Reduced.Gentzen
