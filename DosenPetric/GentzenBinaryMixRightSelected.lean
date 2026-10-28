module

public import DosenPetric.GentzenBinaryMixRightNative

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace BinaryMix

def rightFirstAt {Γ Θ Δ Λ I D : List (NormalForm P)} {C : NormalForm P}
    (a : At Γ C) (g : G P Θ Λ) (k : G P (a.erase ++ I) (Δ ++ D)) :
    G P ((At.shift Θ a).erase ++ I) ((Λ ++ Δ) ++ D) :=
  (rightLeading g k).reindex
    (congrArg (fun xs => xs ++ I) (At.erase_shift_at Θ a)).symm rfl

theorem rightFirstAt_equation {Γ Θ Δ Λ I J : List (NormalForm P)} {C : NormalForm P}
    (f : G P Γ Δ) (g : G P Θ Λ) (h : G P I J) (z : At J C) (a : At Γ C) :
    ofTerm (PositionalCut.cut h z (G.mix f g) (At.shift Θ a)).denote =
      ofTerm (rightFirstAt a g (PositionalCut.cut h z f a)).denote := by
  apply G.reindex_left_cancel_denote
    (congrArg (fun xs => xs ++ I) (At.erase_shift_at Θ a))
  rw [PositionalCut.reindex_residues h z _ _ rfl (At.erase_shift_at Θ a)]
  change ofTerm (G.cut (z.toHead.right h)
    ((LogicalDeletion.headShift Θ a).left (G.mix f g))).denote = _
  apply (Rules.cut_congr rfl (headShift_mix f a g)).trans
  exact rightLeading_equation (z.toHead.right h) g (a.toHead.left f)

theorem rightFirstAt_count {Γ Θ Δ Λ I D : List (NormalForm P)} {C : NormalForm P}
    (a : At Γ C) (g : G P Θ Λ) (k : G P (a.erase ++ I) (Δ ++ D)) :
    (rightFirstAt a g k).cutCount = k.cutCount + g.cutCount := by
  simp only [rightFirstAt,rightLeading,G.count_reindex,ExchangeScript.right_count,
    ExchangeScript.left_count,G.cutCount]

theorem rightFirstAt_atomized {Γ Θ Δ Λ I D : List (NormalForm P)} {C : NormalForm P}
    (a : At Γ C) (g : G P Θ Λ) (k : G P (a.erase ++ I) (Δ ++ D)) :
    (rightFirstAt a g k).Atomized ↔ k.Atomized ∧ g.Atomized := by
  simp only [rightFirstAt,rightLeading,G.atomized_reindex,ExchangeScript.right_atomized,
    ExchangeScript.left_atomized,G.Atomized]

theorem rightFirstAt_congr {Γ Θ Δ Λ I D : List (NormalForm P)} {C : NormalForm P}
    (a : At Γ C) (g : G P Θ Λ) (k k' : G P (a.erase ++ I) (Δ ++ D))
    (hk : ofTerm k.denote = ofTerm k'.denote) :
    ofTerm (rightFirstAt a g k).denote = ofTerm (rightFirstAt a g k').denote := by
  unfold rightFirstAt
  apply G.reindex_congr
  unfold rightLeading
  rw [ExchangeScript.right_denote,ExchangeScript.left_denote,
    ExchangeScript.right_denote,ExchangeScript.left_denote]
  change comp (comp _ (ofTerm (Rules.mix k.denote g.denote))) _ = _
  rw [Rules.mix_congr hk rfl]
  rfl

end BinaryMix
end DosenPetric.Reduced.Gentzen
