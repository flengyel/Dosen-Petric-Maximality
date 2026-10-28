module

public import DosenPetric.GentzenConjFirstEquation

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace BinaryLogical

theorem fixed_suffix_conjR {F U Θ Δ Λ : List (NormalForm P)} {A B : NormalForm P}
    (p : StructuralProgram P F U) (f : G P U (A :: Δ)) (g : G P Θ (B :: Λ)) :
    ofTerm ((p.suffixFixed Θ).left (G.conjR f g)).denote =
      ofTerm (G.conjR (p.left f) g).denote := by
  rw [StructuralProgram.left_denote,G.denote_conjR,G.denote_conjR]
  simp only [Rules.conjRight,ofTerm_comp,ofTerm_tensor,ofTerm_id]
  rw [StructuralProgram.left_denote]
  have he : comp ((p.suffixFixed Θ).arrow .conj) (ofTerm (append .conj U Θ).invTerm) =
      comp (ofTerm (append .conj F Θ).invTerm)
        (tensor .conj (p.arrow .conj) (id (ante Θ))) := p.suffixFixed_split .conj Θ
  rw [← Laws.assoc,he]
  simp only [Laws.assoc]
  rw [← Laws.assoc (tensor .conj (p.arrow .conj) (id (ante Θ))),Laws.tensor_comp,Laws.id_comp]

theorem headBefore_conjR {Γ Θ Δ Λ : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P Γ (A :: Δ)) (a : At Γ C) (g : G P Θ (B :: Λ)) :
    ofTerm ((LogicalDeletion.headBefore a Θ).left (G.conjR f g)).denote =
      ofTerm (G.conjR (a.toHead.left f) g).denote := by
  rw [ExchangeScript.left_denote,BinaryMix.headBefore_structural]
  have he := fixed_suffix_conjR a.toHead.structural f g
  rw [StructuralProgram.left_denote] at he
  change comp ((a.toHead.structural.suffixFixed Θ).arrow .conj) (ofTerm (G.conjR f g).denote) = _
  rw [he]
  have ha : ofTerm (a.toHead.structural.left f).denote = ofTerm (a.toHead.left f).denote := by
    rw [StructuralProgram.left_denote,ExchangeScript.left_denote,ExchangeScript.structural_arrow]
  exact Rules.conjRight_congr ha rfl

def conjRRightFirst {Γ Θ Δ Λ I D : List (NormalForm P)} {A B C : NormalForm P}
    (a : At Γ C) (g : G P Θ (B :: Λ)) (k : G P (a.erase ++ I) ((A :: Δ) ++ D)) :
    G P ((a.before Θ).erase ++ I) ((.conj A B :: (Δ ++ Λ)) ++ D) :=
  (conjFirstNative k g).reindex
    (congrArg (fun xs => xs ++ I) (a.erase_before Θ)).symm rfl

theorem conjRRightFirst_equation {Γ Θ Δ Λ I J : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P Γ (A :: Δ)) (g : G P Θ (B :: Λ)) (h : G P I J) (z : At J C) (a : At Γ C) :
    ofTerm (PositionalCut.cut h z (G.conjR f g) (a.before Θ)).denote =
      ofTerm (conjRRightFirst a g (PositionalCut.cut h z f a)).denote := by
  apply G.reindex_left_cancel_denote
    (congrArg (fun xs => xs ++ I) (a.erase_before Θ))
  rw [PositionalCut.reindex_residues h z _ _ rfl (a.erase_before Θ)]
  change ofTerm (G.cut (z.toHead.right h)
    ((LogicalDeletion.headBefore a Θ).left (G.conjR f g))).denote = _
  apply (Rules.cut_congr rfl (headBefore_conjR f a g)).trans
  exact conjFirstNative_equation (a.toHead.left f) g (z.toHead.right h)

theorem conjRRightFirst_count {Γ Θ Δ Λ I D : List (NormalForm P)} {A B C : NormalForm P}
    (a : At Γ C) (g : G P Θ (B :: Λ)) (k : G P (a.erase ++ I) ((A :: Δ) ++ D)) :
    (conjRRightFirst a g k).cutCount = k.cutCount + g.cutCount := by
  simp only [conjRRightFirst,conjFirstNative,G.count_reindex,ExchangeScript.right_count,
    ExchangeScript.left_count,G.cutCount]

theorem conjRRightFirst_atomized {Γ Θ Δ Λ I D : List (NormalForm P)} {A B C : NormalForm P}
    (a : At Γ C) (g : G P Θ (B :: Λ)) (k : G P (a.erase ++ I) ((A :: Δ) ++ D)) :
    (conjRRightFirst a g k).Atomized ↔ k.Atomized ∧ g.Atomized := by
  simp only [conjRRightFirst,conjFirstNative,G.atomized_reindex,ExchangeScript.right_atomized,
    ExchangeScript.left_atomized,G.Atomized]

theorem conjRRightFirst_congr {Γ Θ Δ Λ I D : List (NormalForm P)} {A B C : NormalForm P}
    (a : At Γ C) (g : G P Θ (B :: Λ)) (k k' : G P (a.erase ++ I) ((A :: Δ) ++ D))
    (hk : ofTerm k.denote = ofTerm k'.denote) :
    ofTerm (conjRRightFirst a g k).denote = ofTerm (conjRRightFirst a g k').denote := by
  unfold conjRRightFirst
  apply G.reindex_congr
  unfold conjFirstNative
  rw [ExchangeScript.right_denote,ExchangeScript.left_denote,
    ExchangeScript.right_denote,ExchangeScript.left_denote]
  change comp (comp _ (ofTerm (Rules.conjRight k.denote g.denote))) _ = _
  rw [Rules.conjRight_congr hk rfl]
  rfl

end BinaryLogical
namespace CutCommutation

theorem conjR_right_first_eliminated {Γ Θ Δ Λ I J : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P Γ (A :: Δ)) (g : G P Θ (B :: Λ)) (h : G P I J) (z : At J C) (a : At Γ C)
    (hg : g.CutFree) (ag : g.Atomized) (hs : PositionalCut.Eliminated h z f a) :
    PositionalCut.Eliminated h z (G.conjR f g) (a.before Θ) := by
  obtain ⟨k,hk,ak,ek⟩ := hs
  refine ⟨BinaryLogical.conjRRightFirst a g k,?_,?_,?_⟩
  · change (BinaryLogical.conjRRightFirst a g k).cutCount = 0
    rw [BinaryLogical.conjRRightFirst_count]
    exact Nat.add_eq_zero_iff.mpr ⟨hk,hg⟩
  · exact (BinaryLogical.conjRRightFirst_atomized a g k).mpr ⟨ak,ag⟩
  · exact (BinaryLogical.conjRRightFirst_congr a g k _ ek).trans
      (BinaryLogical.conjRRightFirst_equation f g h z a).symm

theorem conjR_right_first_rank_step {Γ Θ Δ Λ I J : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P Γ (A :: Δ)) (g : G P Θ (B :: Λ)) (h : G P I J) (z : At J C) (a : At Γ C)
    (hc : PositionalCut.Clean h z (G.conjR f g) (a.before Θ))
    (ih : ∀ {K L M N : List (NormalForm P)} (b : G P K L) (v : At L C)
      (d : G P M N) (w : At M C),
      PositionalCut.rank b v d w < PositionalCut.rank h z (G.conjR f g) (a.before Θ) →
      PositionalCut.Clean b v d w → PositionalCut.Eliminated b v d w) :
    PositionalCut.Eliminated h z (G.conjR f g) (a.before Θ) := by
  have hd := PositionalCut.conjR_right_first_descent f g h z a hc
  exact conjR_right_first_eliminated f g h z a ((G.conjR_cutFree f g).mp hc.2.1).2 hc.2.2.2.1.2
    (ih h z f a hd.2 hd.1)

end CutCommutation
end DosenPetric.Reduced.Gentzen
