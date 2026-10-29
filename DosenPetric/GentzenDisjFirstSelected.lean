module

public import DosenPetric.GentzenDisjFirstEquation

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace DisjLogical

theorem residual_first_disjL {F U Γ Θ Λ : List (NormalForm P)} {A B : NormalForm P}
    (p : StructuralProgram P F U) (f : G P (A :: Γ) U) (g : G P (B :: Θ) Λ) :
    ofTerm ((p.suffixFixed Λ).right (G.disjL f g)).denote =
      ofTerm (G.disjL (p.right f) g).denote := by
  rw [StructuralProgram.right_denote,disjL_denote,disjL_denote,StructuralProgram.right_denote]
  have hs := p.suffixFixed_split .disj Λ
  dsimp only [side,sideM,disjMonoidal,opposite,category,split] at hs
  simp only [Laws.assoc]
  rw [hs]
  have hd := disjPair_output (ofTerm f.denote) (ofTerm g.denote) (p.arrow .disj) (id (succ Λ))
  rw [Laws.comp_id] at hd
  erw [← Laws.assoc (disjPair (ofTerm f.denote) (ofTerm g.denote)),hd]

theorem headBefore_disjL {Γ Θ Δ Λ : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P (A :: Γ) Δ) (a : At Δ C) (g : G P (B :: Θ) Λ) :
    ofTerm ((LogicalDeletion.headBefore a Λ).right (G.disjL f g)).denote =
      ofTerm (G.disjL (a.toHead.right f) g).denote := by
  rw [ExchangeScript.right_denote,BinaryMix.headBefore_structural]
  have he := residual_first_disjL a.toHead.structural f g
  rw [StructuralProgram.right_denote] at he
  change comp (ofTerm (G.disjL f g).denote) ((a.toHead.structural.suffixFixed Λ).arrow .disj) = _
  rw [he]
  have ha : ofTerm (a.toHead.structural.right f).denote = ofTerm (a.toHead.right f).denote := by
    rw [StructuralProgram.right_denote,ExchangeScript.right_denote,ExchangeScript.structural_arrow]
  exact Rules.disjLeft_congr ha rfl

def disjLLeftFirst {Γ Θ Δ Λ T J : List (NormalForm P)} {A B C : NormalForm P}
    (a : At Δ C) (g : G P (B :: Θ) Λ) (k : G P (T ++ (A :: Γ)) (J ++ a.erase)) :
    G P (T ++ (.disj A B :: (Γ ++ Θ))) (J ++ (a.before Λ).erase) :=
  (disjFirstNative k g).reindex rfl
    (congrArg (fun xs => J ++ xs) (a.erase_before Λ)).symm

theorem disjLLeftFirst_count {Γ Θ Δ Λ T J : List (NormalForm P)} {A B C : NormalForm P}
    (a : At Δ C) (g : G P (B :: Θ) Λ) (k : G P (T ++ (A :: Γ)) (J ++ a.erase)) :
    (disjLLeftFirst a g k).cutCount = k.cutCount + g.cutCount := by
  simp only [disjLLeftFirst,disjFirstNative,G.count_reindex,
    ExchangeScript.right_count,ExchangeScript.left_count,G.cutCount]

theorem disjLLeftFirst_atomized {Γ Θ Δ Λ T J : List (NormalForm P)} {A B C : NormalForm P}
    (a : At Δ C) (g : G P (B :: Θ) Λ) (k : G P (T ++ (A :: Γ)) (J ++ a.erase)) :
    (disjLLeftFirst a g k).Atomized ↔ k.Atomized ∧ g.Atomized := by
  simp only [disjLLeftFirst,disjFirstNative,G.atomized_reindex,
    ExchangeScript.right_atomized,ExchangeScript.left_atomized,G.Atomized]

theorem disjLLeftFirst_congr {Γ Θ Δ Λ T J : List (NormalForm P)} {A B C : NormalForm P}
    (a : At Δ C) (g : G P (B :: Θ) Λ) (k k' : G P (T ++ (A :: Γ)) (J ++ a.erase))
    (hk : ofTerm k.denote = ofTerm k'.denote) :
    ofTerm (disjLLeftFirst a g k).denote = ofTerm (disjLLeftFirst a g k').denote := by
  unfold disjLLeftFirst
  apply G.reindex_congr
  have ha : ofTerm ((HeadRouting.front T Γ A).left k).denote =
      ofTerm ((HeadRouting.front T Γ A).left k').denote := by
    rw [ExchangeScript.left_denote,ExchangeScript.left_denote,hk]
  unfold disjFirstNative
  rw [ExchangeScript.right_denote,ExchangeScript.left_denote,ExchangeScript.left_denote,
    ExchangeScript.right_denote,ExchangeScript.left_denote,ExchangeScript.left_denote]
  change comp (comp _ (comp _ (ofTerm (Rules.disjLeft _ g.denote)))) _ = _
  rw [Rules.disjLeft_congr ha rfl]
  rfl

theorem disjLLeftFirst_equation {Γ Θ Δ Λ I J : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P (A :: Γ) Δ) (g : G P (B :: Θ) Λ) (a : At Δ C) (h : G P I J) (z : At I C) :
    ofTerm (PositionalCut.cut (G.disjL f g) (a.before Λ) h z).denote =
      ofTerm (disjLLeftFirst a g (PositionalCut.cut f a h z)).denote := by
  apply G.reindex_right_cancel_denote
    (congrArg (fun xs => J ++ xs) (a.erase_before Λ))
  rw [PositionalCut.reindex_residues (G.disjL f g) (a.before Λ) h z (a.erase_before Λ) rfl]
  change ofTerm (G.cut ((LogicalDeletion.headBefore a Λ).right (G.disjL f g))
    (z.toHead.left h)).denote = _
  apply (Rules.cut_congr (headBefore_disjL f a g) rfl).trans
  exact disjFirstNative_equation (a.toHead.right f) g (z.toHead.left h)

end DisjLogical
namespace CutCommutation

theorem disjL_left_first_eliminated {Γ Θ Δ Λ I J : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P (A :: Γ) Δ) (g : G P (B :: Θ) Λ) (a : At Δ C) (h : G P I J) (z : At I C)
    (hg : g.CutFree) (ag : g.Atomized) (hs : PositionalCut.Eliminated f a h z) :
    PositionalCut.Eliminated (G.disjL f g) (a.before Λ) h z := by
  obtain ⟨k,hk,ak,ek⟩ := hs
  refine ⟨DisjLogical.disjLLeftFirst a g k,?_,?_,?_⟩
  · change (DisjLogical.disjLLeftFirst a g k).cutCount = 0
    rw [DisjLogical.disjLLeftFirst_count]
    exact Nat.add_eq_zero_iff.mpr ⟨hk,hg⟩
  · exact (DisjLogical.disjLLeftFirst_atomized a g k).mpr ⟨ak,ag⟩
  · exact (DisjLogical.disjLLeftFirst_congr a g k _ ek).trans
      (DisjLogical.disjLLeftFirst_equation f g a h z).symm

theorem disjL_left_first_rank_step {Γ Θ Δ Λ I J : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P (A :: Γ) Δ) (g : G P (B :: Θ) Λ) (a : At Δ C) (h : G P I J) (z : At I C)
    (hc : PositionalCut.Clean (G.disjL f g) (a.before Λ) h z)
    (ih : ∀ {K L M N : List (NormalForm P)} (b : G P K L) (v : At L C)
      (d : G P M N) (w : At M C),
      PositionalCut.rank b v d w < PositionalCut.rank (G.disjL f g) (a.before Λ) h z →
      PositionalCut.Clean b v d w → PositionalCut.Eliminated b v d w) :
    PositionalCut.Eliminated (G.disjL f g) (a.before Λ) h z := by
  have hd := PositionalCut.disjL_left_first_descent f g a h z hc
  exact disjL_left_first_eliminated f g a h z ((G.disjL_cutFree f g).mp hc.1).2 hc.2.2.1.2
    (ih f a h z hd.2 hd.1)

end CutCommutation
end DosenPetric.Reduced.Gentzen
