module

public import DosenPetric.GentzenDisjSecondEquation

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace DisjLogical

theorem residual_second_disjL {F U Γ Θ Δ : List (NormalForm P)} {A B : NormalForm P}
    (p : StructuralProgram P F U) (f : G P (A :: Γ) Δ) (g : G P (B :: Θ) U) :
    ofTerm ((p.prefixFixed Δ).right (G.disjL f g)).denote =
      ofTerm (G.disjL f (p.right g)).denote := by
  rw [StructuralProgram.right_denote,disjL_denote,disjL_denote,StructuralProgram.right_denote]
  have hs := p.prefixFixed_split .disj Δ
  dsimp only [side,sideM,disjMonoidal,opposite,category,split] at hs
  simp only [Laws.assoc]
  rw [hs]
  have hd := (disjPair_output_second (ofTerm f.denote) (ofTerm g.denote) (p.arrow .disj)).symm
  erw [← Laws.assoc (disjPair (ofTerm f.denote) (ofTerm g.denote)),hd]

theorem headShift_disjL {Γ Θ Δ Λ : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P (A :: Γ) Δ) (g : G P (B :: Θ) Λ) (a : At Λ C) :
    ofTerm ((LogicalDeletion.headShift Δ a).right (G.disjL f g)).denote =
      ofTerm ((HeadRouting.front Δ a.erase C).right (G.disjL f (a.toHead.right g))).denote := by
  rw [ExchangeScript.right_denote,BinaryMix.headShift_structural]
  have he := residual_second_disjL a.toHead.structural f g
  rw [StructuralProgram.right_denote] at he
  change comp (ofTerm (G.disjL f g).denote)
    (comp ((a.toHead.structural.prefixFixed Δ).arrow .disj) ((HeadRouting.front Δ a.erase C).arrow .disj)) = _
  erw [← Laws.assoc,he,ExchangeScript.right_denote]
  have ha : ofTerm (a.toHead.structural.right g).denote = ofTerm (a.toHead.right g).denote := by
    rw [StructuralProgram.right_denote,ExchangeScript.right_denote,ExchangeScript.structural_arrow]
  change comp (ofTerm (Rules.disjLeft f.denote (a.toHead.structural.right g).denote)) _ = _
  rw [Rules.disjLeft_congr rfl ha]
  rfl

def disjLLeftSecond {Γ Θ Δ Λ T J : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P (A :: Γ) Δ) (a : At Λ C) (k : G P (T ++ (B :: Θ)) (J ++ a.erase)) :
    G P (T ++ (.disj A B :: (Γ ++ Θ))) (J ++ (At.shift Δ a).erase) :=
  (disjSecondNative f k).reindex rfl
    (congrArg (fun xs => J ++ xs) (At.erase_shift_at Δ a)).symm

theorem disjLLeftSecond_count {Γ Θ Δ Λ T J : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P (A :: Γ) Δ) (a : At Λ C) (k : G P (T ++ (B :: Θ)) (J ++ a.erase)) :
    (disjLLeftSecond f a k).cutCount = f.cutCount + k.cutCount := by
  simp only [disjLLeftSecond,disjSecondNative,G.count_reindex,
    ExchangeScript.right_count,ExchangeScript.left_count,G.cutCount]

theorem disjLLeftSecond_atomized {Γ Θ Δ Λ T J : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P (A :: Γ) Δ) (a : At Λ C) (k : G P (T ++ (B :: Θ)) (J ++ a.erase)) :
    (disjLLeftSecond f a k).Atomized ↔ f.Atomized ∧ k.Atomized := by
  simp only [disjLLeftSecond,disjSecondNative,G.atomized_reindex,
    ExchangeScript.right_atomized,ExchangeScript.left_atomized,G.Atomized]

theorem disjLLeftSecond_congr {Γ Θ Δ Λ T J : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P (A :: Γ) Δ) (a : At Λ C) (k k' : G P (T ++ (B :: Θ)) (J ++ a.erase))
    (hk : ofTerm k.denote = ofTerm k'.denote) :
    ofTerm (disjLLeftSecond f a k).denote = ofTerm (disjLLeftSecond f a k').denote := by
  unfold disjLLeftSecond
  apply G.reindex_congr
  have ha : ofTerm ((HeadRouting.front T Θ B).left k).denote =
      ofTerm ((HeadRouting.front T Θ B).left k').denote := by
    rw [ExchangeScript.left_denote,ExchangeScript.left_denote,hk]
  unfold disjSecondNative
  rw [ExchangeScript.right_denote,ExchangeScript.left_denote,ExchangeScript.left_denote,
    ExchangeScript.right_denote,ExchangeScript.left_denote,ExchangeScript.left_denote]
  change comp (comp _ (comp _ (ofTerm (Rules.disjLeft f.denote _)))) _ = _
  rw [Rules.disjLeft_congr rfl ha]
  rfl

theorem disjLLeftSecond_equation {Γ Θ Δ Λ I J : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P (A :: Γ) Δ) (g : G P (B :: Θ) Λ) (a : At Λ C) (h : G P I J) (z : At I C) :
    ofTerm (PositionalCut.cut (G.disjL f g) (At.shift Δ a) h z).denote =
      ofTerm (disjLLeftSecond f a (PositionalCut.cut g a h z)).denote := by
  apply G.reindex_right_cancel_denote
    (congrArg (fun xs => J ++ xs) (At.erase_shift_at Δ a))
  rw [PositionalCut.reindex_residues (G.disjL f g) (At.shift Δ a) h z (At.erase_shift_at Δ a) rfl]
  change ofTerm (G.cut ((LogicalDeletion.headShift Δ a).right (G.disjL f g))
    (z.toHead.left h)).denote = _
  apply (Rules.cut_congr (headShift_disjL f g a) rfl).trans
  exact disjSecondNative_equation f (a.toHead.right g) (z.toHead.left h)

end DisjLogical
namespace CutCommutation

theorem disjL_left_second_eliminated {Γ Θ Δ Λ I J : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P (A :: Γ) Δ) (g : G P (B :: Θ) Λ) (a : At Λ C) (h : G P I J) (z : At I C)
    (hf : f.CutFree) (af : f.Atomized) (hs : PositionalCut.Eliminated g a h z) :
    PositionalCut.Eliminated (G.disjL f g) (At.shift Δ a) h z := by
  obtain ⟨k,hk,ak,ek⟩ := hs
  refine ⟨DisjLogical.disjLLeftSecond f a k,?_,?_,?_⟩
  · change (DisjLogical.disjLLeftSecond f a k).cutCount = 0
    rw [DisjLogical.disjLLeftSecond_count]
    exact Nat.add_eq_zero_iff.mpr ⟨hf,hk⟩
  · exact (DisjLogical.disjLLeftSecond_atomized f a k).mpr ⟨af,ak⟩
  · exact (DisjLogical.disjLLeftSecond_congr f a k _ ek).trans
      (DisjLogical.disjLLeftSecond_equation f g a h z).symm

theorem disjL_left_second_rank_step {Γ Θ Δ Λ I J : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P (A :: Γ) Δ) (g : G P (B :: Θ) Λ) (a : At Λ C) (h : G P I J) (z : At I C)
    (hc : PositionalCut.Clean (G.disjL f g) (At.shift Δ a) h z)
    (ih : ∀ {K L M N : List (NormalForm P)} (b : G P K L) (v : At L C)
      (d : G P M N) (w : At M C),
      PositionalCut.rank b v d w < PositionalCut.rank (G.disjL f g) (At.shift Δ a) h z →
      PositionalCut.Clean b v d w → PositionalCut.Eliminated b v d w) :
    PositionalCut.Eliminated (G.disjL f g) (At.shift Δ a) h z := by
  have hd := PositionalCut.disjL_left_second_descent f g a h z hc
  exact disjL_left_second_eliminated f g a h z ((G.disjL_cutFree f g).mp hc.1).1 hc.2.2.1.1
    (ih g a h z hd.2 hd.1)

end CutCommutation
end DosenPetric.Reduced.Gentzen
