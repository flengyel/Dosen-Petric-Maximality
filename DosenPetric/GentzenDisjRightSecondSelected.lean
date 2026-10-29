module

public import DosenPetric.GentzenDisjRightSecondEquation

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace DisjLogical

theorem input_second_disjL {F U Γ Δ Λ : List (NormalForm P)} {A B : NormalForm P}
    (p : StructuralProgram P F U) (f : G P (A :: Γ) Δ) (g : G P (B :: U) Λ) :
    ofTerm (((p.prefixFixed Γ).consFixed (.disj A B)).left (G.disjL f g)).denote =
      ofTerm (G.disjL f ((p.consFixed B).left g)).denote := by
  rw [StructuralProgram.left_denote,disjL_denote,disjL_denote,StructuralProgram.left_denote,
    BinaryLogical.structural_consFixed_arrow,BinaryLogical.structural_consFixed_arrow]
  have hs := p.prefixFixed_split .conj Γ
  dsimp only [side,sideM,conjMonoidal,category,split] at hs ⊢
  rw [← Laws.assoc (tensor .conj (id (.disj A B)) ((p.prefixFixed Γ).arrow .conj)),
    Laws.tensor_comp,Laws.id_comp,hs,tensor_factor .conj (id (.disj A B))]
  have hd := (disjPair_input_second (p.arrow .conj) (ofTerm f.denote) (ofTerm g.denote)).symm
  simp only [Laws.assoc]
  erw [← Laws.assoc (tensor .conj (id (.disj A B)) (tensor .conj (id (ante Γ)) (p.arrow .conj))),hd]

theorem headShift_input_disjL {Γ Θ Δ Λ : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P (A :: Γ) Δ) (g : G P (B :: Θ) Λ) (a : At Θ C) :
    ofTerm ((LogicalDeletion.headShift (.disj A B :: Γ) a).left (G.disjL f g)).denote =
      ofTerm ((HeadRouting.front (.disj A B :: Γ) a.erase C).left
        (G.disjL f ((a.toHead.consFixed B).left g))).denote := by
  rw [ExchangeScript.left_denote,BinaryMix.headShift_structural]
  have he := input_second_disjL a.toHead.structural f g
  rw [StructuralProgram.left_denote] at he
  change comp (comp ((HeadRouting.front (.disj A B :: Γ) a.erase C).arrow .conj)
    ((a.toHead.structural.prefixFixed (.disj A B :: Γ)).arrow .conj)) (ofTerm (G.disjL f g).denote) = _
  rw [Laws.assoc]
  erw [he,ExchangeScript.left_denote]
  have ha : ofTerm ((a.toHead.structural.consFixed B).left g).denote =
      ofTerm ((a.toHead.consFixed B).left g).denote := by
    rw [StructuralProgram.left_denote,ExchangeScript.left_denote,BinaryLogical.structural_consFixed_arrow,
      ExchangeScript.consFixed_arrow,ExchangeScript.structural_arrow]
  change comp _ (ofTerm (Rules.disjLeft f.denote (a.toHead.structural.consFixed B |>.left g).denote)) = _
  rw [Rules.disjLeft_congr rfl ha]
  rfl

theorem rightChild_factor {Θ Λ I J : List (NormalForm P)} {B C : NormalForm P}
    (h : G P I J) (z : At J C) (g : G P (B :: Θ) Λ) (a : At Θ C) :
    ofTerm (PositionalCut.cut h z g a.there).denote =
      ofTerm (G.cut (z.toHead.right h)
        ((HeadRouting.front [B] a.erase C).left ((a.toHead.consFixed B).left g))).denote := by
  apply Rules.cut_congr rfl
  rw [ExchangeScript.left_denote,BinaryLogical.toHead_there_arrow,
    ExchangeScript.left_denote,ExchangeScript.left_denote]
  simp only [ExchangeScript.arrow,ExchangeScript.rewire,Rewire.arrow]
  dsimp only [side,category]
  exact Laws.assoc ..

theorem disjRightSecondNative_congr {Γ Θ Δ Λ I D : List (NormalForm P)} {A B : NormalForm P}
    (f : G P (A :: Γ) Δ) (k k' : G P (B :: (Θ ++ I)) (Λ ++ D))
    (hk : ofTerm k.denote = ofTerm k'.denote) :
    ofTerm (disjRightSecondNative f k).denote = ofTerm (disjRightSecondNative f k').denote := by
  unfold disjRightSecondNative
  rw [ExchangeScript.right_denote,ExchangeScript.left_denote,
    ExchangeScript.right_denote,ExchangeScript.left_denote]
  change comp (comp _ (ofTerm (Rules.disjLeft f.denote k.denote))) _ = _
  rw [Rules.disjLeft_congr rfl hk]
  rfl

def disjLRightSecond {Γ Θ Δ Λ I D : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P (A :: Γ) Δ) (a : At Θ C) (k : G P (B :: (a.erase ++ I)) (Λ ++ D)) :
    G P ((At.shift (.disj A B :: Γ) a).erase ++ I) ((Δ ++ Λ) ++ D) :=
  (disjRightSecondNative f k).reindex
    (congrArg (fun xs => xs ++ I) (At.erase_shift_at (.disj A B :: Γ) a)).symm rfl

theorem disjLRightSecond_count {Γ Θ Δ Λ I D : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P (A :: Γ) Δ) (a : At Θ C) (k : G P (B :: (a.erase ++ I)) (Λ ++ D)) :
    (disjLRightSecond f a k).cutCount = f.cutCount + k.cutCount := by
  simp only [disjLRightSecond,disjRightSecondNative,G.count_reindex,
    ExchangeScript.right_count,ExchangeScript.left_count,G.cutCount]

theorem disjLRightSecond_atomized {Γ Θ Δ Λ I D : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P (A :: Γ) Δ) (a : At Θ C) (k : G P (B :: (a.erase ++ I)) (Λ ++ D)) :
    (disjLRightSecond f a k).Atomized ↔ f.Atomized ∧ k.Atomized := by
  simp only [disjLRightSecond,disjRightSecondNative,G.atomized_reindex,
    ExchangeScript.right_atomized,ExchangeScript.left_atomized,G.Atomized]

theorem disjLRightSecond_congr {Γ Θ Δ Λ I D : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P (A :: Γ) Δ) (a : At Θ C) (k k' : G P (B :: (a.erase ++ I)) (Λ ++ D))
    (hk : ofTerm k.denote = ofTerm k'.denote) :
    ofTerm (disjLRightSecond f a k).denote = ofTerm (disjLRightSecond f a k').denote := by
  unfold disjLRightSecond
  apply G.reindex_congr
  unfold disjRightSecondNative
  rw [ExchangeScript.right_denote,ExchangeScript.left_denote,
    ExchangeScript.right_denote,ExchangeScript.left_denote]
  change comp (comp _ (ofTerm (Rules.disjLeft f.denote k.denote))) _ = _
  rw [Rules.disjLeft_congr rfl hk]
  rfl

theorem disjLRightSecond_equation {Γ Θ Δ Λ I J : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P (A :: Γ) Δ) (g : G P (B :: Θ) Λ) (h : G P I J) (z : At J C) (a : At Θ C) :
    ofTerm (PositionalCut.cut h z (G.disjL f g) (At.shift (.disj A B :: Γ) a)).denote =
      ofTerm (disjLRightSecond f a (PositionalCut.cut h z g a.there)).denote := by
  apply G.reindex_left_cancel_denote
    (congrArg (fun xs => xs ++ I) (At.erase_shift_at (.disj A B :: Γ) a))
  rw [PositionalCut.reindex_residues h z (G.disjL f g) (At.shift (.disj A B :: Γ) a)
    rfl (At.erase_shift_at (.disj A B :: Γ) a)]
  change ofTerm (G.cut (z.toHead.right h)
    ((LogicalDeletion.headShift (.disj A B :: Γ) a).left (G.disjL f g))).denote = _
  apply (Rules.cut_congr rfl (headShift_input_disjL f g a)).trans
  apply (disjRightSecondNative_equation f ((a.toHead.consFixed B).left g) (z.toHead.right h)).trans
  exact disjRightSecondNative_congr f _ _ (rightChild_factor h z g a).symm

end DisjLogical
namespace CutCommutation

theorem disjL_right_second_eliminated {Γ Θ Δ Λ I J : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P (A :: Γ) Δ) (g : G P (B :: Θ) Λ) (h : G P I J) (z : At J C) (a : At Θ C)
    (hf : f.CutFree) (af : f.Atomized) (hs : PositionalCut.Eliminated h z g a.there) :
    PositionalCut.Eliminated h z (G.disjL f g) (At.shift (.disj A B :: Γ) a) := by
  obtain ⟨k,hk,ak,ek⟩ := hs
  refine ⟨DisjLogical.disjLRightSecond f a k,?_,?_,?_⟩
  · change (DisjLogical.disjLRightSecond f a k).cutCount = 0
    rw [DisjLogical.disjLRightSecond_count]
    exact Nat.add_eq_zero_iff.mpr ⟨hf,hk⟩
  · exact (DisjLogical.disjLRightSecond_atomized f a k).mpr ⟨af,ak⟩
  · exact (DisjLogical.disjLRightSecond_congr f a k _ ek).trans
      (DisjLogical.disjLRightSecond_equation f g h z a).symm

theorem disjL_right_second_rank_step {Γ Θ Δ Λ I J : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P (A :: Γ) Δ) (g : G P (B :: Θ) Λ) (h : G P I J) (z : At J C) (a : At Θ C)
    (hc : PositionalCut.Clean h z (G.disjL f g) (At.shift (.disj A B :: Γ) a))
    (ih : ∀ {K L M N : List (NormalForm P)} (b : G P K L) (v : At L C)
      (d : G P M N) (w : At M C),
      PositionalCut.rank b v d w < PositionalCut.rank h z (G.disjL f g) (At.shift (.disj A B :: Γ) a) →
      PositionalCut.Clean b v d w → PositionalCut.Eliminated b v d w) :
    PositionalCut.Eliminated h z (G.disjL f g) (At.shift (.disj A B :: Γ) a) := by
  have hd := PositionalCut.disjL_right_second_descent f g h z a hc
  exact disjL_right_second_eliminated f g h z a ((G.disjL_cutFree f g).mp hc.2.1).1 hc.2.2.2.1.1
    (ih h z g a.there hd.2 hd.1)

end CutCommutation
end DosenPetric.Reduced.Gentzen
