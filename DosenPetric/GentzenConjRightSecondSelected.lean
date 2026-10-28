module

public import DosenPetric.GentzenConjRightSecondParent

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace BinaryLogical

theorem fixed_prefix_conjR {Γ F U Δ Λ : List (NormalForm P)} {A B : NormalForm P}
    (p : StructuralProgram P F U) (f : G P Γ (A :: Δ)) (g : G P U (B :: Λ)) :
    ofTerm ((p.prefixFixed Γ).left (G.conjR f g)).denote =
      ofTerm (G.conjR f (p.left g)).denote := by
  rw [StructuralProgram.left_denote,G.denote_conjR,G.denote_conjR]
  simp only [Rules.conjRight,ofTerm_comp,ofTerm_tensor,ofTerm_id]
  rw [StructuralProgram.left_denote]
  have he : comp ((p.prefixFixed Γ).arrow .conj) (ofTerm (append .conj Γ U).invTerm) =
      comp (ofTerm (append .conj Γ F).invTerm)
        (tensor .conj (id (ante Γ)) (p.arrow .conj)) := p.prefixFixed_split .conj Γ
  rw [← Laws.assoc,he]
  simp only [Laws.assoc]
  rw [← Laws.assoc (tensor .conj (id (ante Γ)) (p.arrow .conj)),Laws.tensor_comp,Laws.id_comp]

theorem headShift_conjR {Γ Θ Δ Λ : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P Γ (A :: Δ)) (g : G P Θ (B :: Λ)) (a : At Θ C) :
    ofTerm ((LogicalDeletion.headShift Γ a).left (G.conjR f g)).denote =
      ofTerm ((HeadRouting.front Γ a.erase C).left (G.conjR f (a.toHead.left g))).denote := by
  rw [ExchangeScript.left_denote,BinaryMix.headShift_structural]
  have he := fixed_prefix_conjR a.toHead.structural f g
  rw [StructuralProgram.left_denote] at he
  change comp (comp ((HeadRouting.front Γ a.erase C).arrow .conj)
    ((a.toHead.structural.prefixFixed Γ).arrow .conj)) (ofTerm (G.conjR f g).denote) = _
  rw [Laws.assoc,he,ExchangeScript.left_denote]
  have ha : ofTerm (a.toHead.structural.left g).denote = ofTerm (a.toHead.left g).denote := by
    rw [StructuralProgram.left_denote,ExchangeScript.left_denote,ExchangeScript.structural_arrow]
  have hh : ofTerm (Rules.conjRight f.denote (a.toHead.structural.left g).denote) =
      ofTerm (Rules.conjRight f.denote (a.toHead.left g).denote) := Rules.conjRight_congr rfl ha
  change comp _ (ofTerm (Rules.conjRight f.denote (a.toHead.structural.left g).denote)) = _
  rw [hh]
  rfl

def conjRRightSecond {Γ Θ Δ Λ I D : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P Γ (A :: Δ)) (a : At Θ C) (k : G P (a.erase ++ I) ((B :: Λ) ++ D)) :
    G P ((At.shift Γ a).erase ++ I) ((.conj A B :: (Δ ++ Λ)) ++ D) :=
  (conjSecondNative f k).reindex
    (congrArg (fun xs => xs ++ I) (At.erase_shift_at Γ a)).symm rfl

theorem conjRRightSecond_equation {Γ Θ Δ Λ I J : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P Γ (A :: Δ)) (g : G P Θ (B :: Λ)) (h : G P I J) (z : At J C) (a : At Θ C) :
    ofTerm (PositionalCut.cut h z (G.conjR f g) (At.shift Γ a)).denote =
      ofTerm (conjRRightSecond f a (PositionalCut.cut h z g a)).denote := by
  apply G.reindex_left_cancel_denote
    (congrArg (fun xs => xs ++ I) (At.erase_shift_at Γ a))
  rw [PositionalCut.reindex_residues h z _ _ rfl (At.erase_shift_at Γ a)]
  change ofTerm (G.cut (z.toHead.right h)
    ((LogicalDeletion.headShift Γ a).left (G.conjR f g))).denote = _
  apply (Rules.cut_congr rfl (headShift_conjR f g a)).trans
  exact conjSecondNative_equation f (a.toHead.left g) (z.toHead.right h)

theorem conjRRightSecond_count {Γ Θ Δ Λ I D : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P Γ (A :: Δ)) (a : At Θ C) (k : G P (a.erase ++ I) ((B :: Λ) ++ D)) :
    (conjRRightSecond f a k).cutCount = f.cutCount + k.cutCount := by
  simp only [conjRRightSecond,conjSecondNative,G.count_reindex,ExchangeScript.right_count,
    ExchangeScript.left_count,G.cutCount]

theorem conjRRightSecond_atomized {Γ Θ Δ Λ I D : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P Γ (A :: Δ)) (a : At Θ C) (k : G P (a.erase ++ I) ((B :: Λ) ++ D)) :
    (conjRRightSecond f a k).Atomized ↔ f.Atomized ∧ k.Atomized := by
  simp only [conjRRightSecond,conjSecondNative,G.atomized_reindex,ExchangeScript.right_atomized,
    ExchangeScript.left_atomized,G.Atomized]

theorem conjRRightSecond_congr {Γ Θ Δ Λ I D : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P Γ (A :: Δ)) (a : At Θ C) (k k' : G P (a.erase ++ I) ((B :: Λ) ++ D))
    (hk : ofTerm k.denote = ofTerm k'.denote) :
    ofTerm (conjRRightSecond f a k).denote = ofTerm (conjRRightSecond f a k').denote := by
  unfold conjRRightSecond
  apply G.reindex_congr
  unfold conjSecondNative
  rw [ExchangeScript.right_denote,ExchangeScript.left_denote,
    ExchangeScript.right_denote,ExchangeScript.left_denote]
  change comp (comp _ (ofTerm (Rules.conjRight f.denote k.denote))) _ = _
  rw [Rules.conjRight_congr rfl hk]
  rfl

end BinaryLogical
namespace CutCommutation

theorem conjR_right_second_eliminated {Γ Θ Δ Λ I J : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P Γ (A :: Δ)) (g : G P Θ (B :: Λ)) (h : G P I J) (z : At J C) (a : At Θ C)
    (hf : f.CutFree) (af : f.Atomized) (hs : PositionalCut.Eliminated h z g a) :
    PositionalCut.Eliminated h z (G.conjR f g) (At.shift Γ a) := by
  obtain ⟨k,hk,ak,ek⟩ := hs
  refine ⟨BinaryLogical.conjRRightSecond f a k,?_,?_,?_⟩
  · change (BinaryLogical.conjRRightSecond f a k).cutCount = 0
    rw [BinaryLogical.conjRRightSecond_count]
    exact Nat.add_eq_zero_iff.mpr ⟨hf,hk⟩
  · exact (BinaryLogical.conjRRightSecond_atomized f a k).mpr ⟨af,ak⟩
  · exact (BinaryLogical.conjRRightSecond_congr f a k _ ek).trans
      (BinaryLogical.conjRRightSecond_equation f g h z a).symm

theorem conjR_right_second_rank_step {Γ Θ Δ Λ I J : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P Γ (A :: Δ)) (g : G P Θ (B :: Λ)) (h : G P I J) (z : At J C) (a : At Θ C)
    (hc : PositionalCut.Clean h z (G.conjR f g) (At.shift Γ a))
    (ih : ∀ {K L M N : List (NormalForm P)} (b : G P K L) (v : At L C)
      (d : G P M N) (w : At M C),
      PositionalCut.rank b v d w < PositionalCut.rank h z (G.conjR f g) (At.shift Γ a) →
      PositionalCut.Clean b v d w → PositionalCut.Eliminated b v d w) :
    PositionalCut.Eliminated h z (G.conjR f g) (At.shift Γ a) := by
  have hd := PositionalCut.conjR_right_second_descent f g h z a hc
  exact conjR_right_second_eliminated f g h z a ((G.conjR_cutFree f g).mp hc.2.1).1 hc.2.2.2.1.1
    (ih h z g a hd.2 hd.1)

end CutCommutation
end DosenPetric.Reduced.Gentzen
