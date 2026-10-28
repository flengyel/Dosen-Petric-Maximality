module

public import DosenPetric.GentzenSameSideLogicalPrefix

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace SameSideLogical

/-- Rebuild conjunction-left after deleting a selected suffix occurrence. -/
def conjTail {Γ F U Λ D : List (NormalForm P)} {A B C : NormalForm P}
    (a : At U C) (f : G P ((At.shift F (At.shift [A,B] a)).erase ++ Γ) (Λ ++ D)) :
    G P ((At.shift F (At.shift [.conj A B] a)).erase ++ Γ) (Λ ++ D) :=
  (SuffixedLogical.conjL F a.erase Γ (Λ ++ D) A B
    (f.reindex (congrArg (fun xs => xs ++ Γ) (At.erase_shift_twice F [A,B] a)) rfl)).reindex
      (congrArg (fun xs => xs ++ Γ) (At.erase_shift_twice F [.conj A B] a)).symm rfl

/-- Rebuild disjunction-right after deleting a selected suffix occurrence. -/
def disjTail {I F U Λ : List (NormalForm P)} {A B C : NormalForm P}
    (a : At U C) (f : G P I (Λ ++ (At.shift F (At.shift [A,B] a)).erase)) :
    G P I (Λ ++ (At.shift F (At.shift [.disj A B] a)).erase) :=
  (PrefixedLogical.disjR I Λ F a.erase A B
    (f.reindex rfl (congrArg (fun xs => Λ ++ xs) (At.erase_shift_twice F [A,B] a)))).reindex
      rfl (congrArg (fun xs => Λ ++ xs) (At.erase_shift_twice F [.disj A B] a)).symm

end SameSideLogical
namespace CutCommutation

/-- Exact positional conjunction-left suffix commutation at the original proof node. -/
theorem same_conjL_tail {Γ Δ F U Λ : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P Γ Δ) (x : At Δ C) (g : G P (F ++ A :: B :: U) Λ) (a : At U C) :
    ofTerm (PositionalCut.cut f x (G.conjL F U Λ A B g) (At.shift F (At.shift [.conj A B] a))).denote =
      ofTerm (SameSideLogical.conjTail a
        (PositionalCut.cut f x g (At.shift F (At.shift [A,B] a)))).denote := by
  apply G.reindex_left_cancel_denote
    (congrArg (fun xs => xs ++ Γ) (At.erase_shift_twice F [.conj A B] a))
  rw [PositionalCut.reindex_residues f x _ _ rfl (At.erase_shift_twice F [.conj A B] a)]
  change ofTerm (G.cut (x.toHead.right f)
    ((LogicalDeletion.headUnder F [.conj A B] a).left (G.conjL F U Λ A B g))).denote = _
  rw [PositionalCut.reindex_residues f x g _ rfl (At.erase_shift_twice F [A,B] a)]
  exact same_conjL_head (x.toHead.right f) g _ _
    (LogicalDeletion.tail_square .conj F A B a)

/-- Exact positional disjunction-right suffix commutation with every adapter explicit. -/
theorem same_disjR_tail {Γ F U Θ Λ : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P Γ (F ++ A :: B :: U)) (a : At U C) (g : G P Θ Λ) (y : At Θ C) :
    ofTerm (PositionalCut.cut (G.disjR Γ F U A B f) (At.shift F (At.shift [.disj A B] a)) g y).denote =
      ofTerm (SameSideLogical.disjTail a
        (PositionalCut.cut f (At.shift F (At.shift [A,B] a)) g y)).denote := by
  apply G.reindex_right_cancel_denote
    (congrArg (fun xs => Λ ++ xs) (At.erase_shift_twice F [.disj A B] a))
  rw [PositionalCut.reindex_residues _ _ g y (At.erase_shift_twice F [.disj A B] a) rfl]
  change ofTerm (G.cut ((LogicalDeletion.headUnder F [.disj A B] a).right
    (G.disjR Γ F U A B f)) (y.toHead.left g)).denote = _
  rw [PositionalCut.reindex_residues f _ g y (At.erase_shift_twice F [A,B] a) rfl]
  exact same_disjR_head f (y.toHead.left g) _ _
    (LogicalDeletion.tail_square .disj F A B a)

end CutCommutation
end DosenPetric.Reduced.Gentzen
