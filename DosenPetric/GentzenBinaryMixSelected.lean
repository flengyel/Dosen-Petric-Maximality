module

public import DosenPetric.GentzenBinaryMixRoutes

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace BinaryMix

theorem fixed_suffix_mix {F U Γ Θ Λ : List (NormalForm P)}
    (p : StructuralProgram P F U) (f : G P Γ U) (g : G P Θ Λ) :
    ofTerm ((p.suffixFixed Λ).right (G.mix g f)).denote =
      ofTerm (G.mix g (p.right f)).denote := by
  rw [StructuralProgram.right_denote]
  change comp (ofTerm (Rules.mix g.denote f.denote)) _ =
    ofTerm (Rules.mix g.denote (p.right f).denote)
  simp only [Rules.mix,ofTerm_comp,ofTerm_tensor,mix_term]
  rw [StructuralProgram.right_denote]
  have he : comp (ofTerm (append .disj U Λ).toTerm) ((p.suffixFixed Λ).arrow .disj) =
      comp (tensor .disj (p.arrow .disj) (id (succ Λ))) (ofTerm (append .disj F Λ).toTerm) :=
    p.suffixFixed_split .disj Λ
  simp only [Laws.assoc]
  erw [he]
  rw [← Laws.assoc (mix (succ U) (succ Λ)),Laws.mix_nat]
  simp only [Laws.assoc]
  rw [← Laws.assoc (tensor .conj (ofTerm f.denote) (ofTerm g.denote)),Laws.tensor_comp,Laws.comp_id]

theorem headBefore_mix {Γ Θ Δ Λ : List (NormalForm P)} {C : NormalForm P}
    (f : G P Γ Δ) (a : At Δ C) (g : G P Θ Λ) :
    ofTerm ((LogicalDeletion.headBefore a Λ).right (G.mix g f)).denote =
      ofTerm (G.mix g (a.toHead.right f)).denote := by
  have he : ofTerm ((LogicalDeletion.headBefore a Λ).right (G.mix g f)).denote =
      ofTerm ((a.toHead.structural.suffixFixed Λ).right (G.mix g f)).denote := by
    rw [ExchangeScript.right_denote,StructuralProgram.right_denote,headBefore_structural]
    rfl
  apply he.trans
  apply (fixed_suffix_mix a.toHead.structural f g).trans
  apply Rules.mix_congr rfl
  rw [StructuralProgram.right_denote,ExchangeScript.right_denote,ExchangeScript.structural_arrow]

/-- The leading-output reconstruction at an arbitrary original selected child tag. -/
def leadingAt {Γ Θ Δ Λ T J : List (NormalForm P)} {C : NormalForm P}
    (a : At Δ C) (g : G P Θ Λ) (k : G P (T ++ Γ) (J ++ a.erase)) :
    G P (T ++ (Γ ++ Θ)) (J ++ (a.before Λ).erase) :=
  (leading g k).reindex rfl (congrArg (fun xs => J ++ xs) (a.erase_before Λ)).symm

theorem leadingAt_equation {Γ Θ Δ Λ I J : List (NormalForm P)} {C : NormalForm P}
    (f : G P Γ Δ) (a : At Δ C) (g : G P Θ Λ) (h : G P I J) (z : At I C) :
    ofTerm (PositionalCut.cut (G.mix g f) (a.before Λ) h z).denote =
      ofTerm (leadingAt a g (PositionalCut.cut f a h z)).denote := by
  apply G.reindex_right_cancel_denote
    (congrArg (fun xs => J ++ xs) (a.erase_before Λ))
  rw [PositionalCut.reindex_residues _ _ h z (a.erase_before Λ) rfl]
  change ofTerm (G.cut ((LogicalDeletion.headBefore a Λ).right (G.mix g f))
    (z.toHead.left h)).denote = _
  apply (Rules.cut_congr (headBefore_mix f a g) rfl).trans
  exact leading_equation (a.toHead.right f) g (z.toHead.left h)

theorem leadingAt_count {Γ Θ Δ Λ T J : List (NormalForm P)} {C : NormalForm P}
    (a : At Δ C) (g : G P Θ Λ) (k : G P (T ++ Γ) (J ++ a.erase)) :
    (leadingAt a g k).cutCount = k.cutCount + g.cutCount := by
  simp only [leadingAt,leading,G.count_reindex,ExchangeScript.right_count,
    ExchangeScript.left_count,G.cutCount]
  omega

theorem leadingAt_atomized {Γ Θ Δ Λ T J : List (NormalForm P)} {C : NormalForm P}
    (a : At Δ C) (g : G P Θ Λ) (k : G P (T ++ Γ) (J ++ a.erase)) :
    (leadingAt a g k).Atomized ↔ k.Atomized ∧ g.Atomized := by
  simp only [leadingAt,leading,G.atomized_reindex,ExchangeScript.right_atomized,
    ExchangeScript.left_atomized,G.Atomized]
  exact And.comm

theorem leadingAt_congr {Γ Θ Δ Λ T J : List (NormalForm P)} {C : NormalForm P}
    (a : At Δ C) (g : G P Θ Λ) (k k' : G P (T ++ Γ) (J ++ a.erase))
    (hk : ofTerm k.denote = ofTerm k'.denote) :
    ofTerm (leadingAt a g k).denote = ofTerm (leadingAt a g k').denote := by
  unfold leadingAt
  apply G.reindex_congr
  unfold leading
  rw [ExchangeScript.right_denote,ExchangeScript.left_denote,
    ExchangeScript.right_denote,ExchangeScript.left_denote]
  change comp (comp _ (ofTerm (Rules.mix g.denote k.denote))) _ = _
  rw [Rules.mix_congr rfl hk]
  rfl

end BinaryMix
end DosenPetric.Reduced.Gentzen
