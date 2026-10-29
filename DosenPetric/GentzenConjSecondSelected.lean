module

public import DosenPetric.GentzenConjSecondRoutes

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace BinaryLogical

def conjRLeftSecond {Γ Θ Δ Λ T J : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P Γ (A :: Δ)) (a : At Λ C) (k : G P (T ++ Θ) (J ++ (B :: a.erase))) :
    G P (T ++ (Γ ++ Θ)) (J ++ (At.shift (.conj A B :: Δ) a).erase) :=
  (conjLeftSecondNative f k).reindex rfl
    (congrArg (fun xs => J ++ xs) (At.erase_shift_at (.conj A B :: Δ) a)).symm

theorem conjRLeftSecond_count {Γ Θ Δ Λ T J : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P Γ (A :: Δ)) (a : At Λ C) (k : G P (T ++ Θ) (J ++ (B :: a.erase))) :
    (conjRLeftSecond f a k).cutCount = f.cutCount + k.cutCount := by
  rw [conjRLeftSecond,G.count_reindex,conjLeftSecondNative_count]

theorem conjRLeftSecond_atomized {Γ Θ Δ Λ T J : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P Γ (A :: Δ)) (a : At Λ C) (k : G P (T ++ Θ) (J ++ (B :: a.erase))) :
    (conjRLeftSecond f a k).Atomized ↔ f.Atomized ∧ k.Atomized := by
  rw [conjRLeftSecond,G.atomized_reindex,conjLeftSecondNative_atomized]

theorem conjRLeftSecond_congr {Γ Θ Δ Λ T J : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P Γ (A :: Δ)) (a : At Λ C) (k k' : G P (T ++ Θ) (J ++ (B :: a.erase)))
    (hk : ofTerm k.denote = ofTerm k'.denote) :
    ofTerm (conjRLeftSecond f a k).denote = ofTerm (conjRLeftSecond f a k').denote := by
  unfold conjRLeftSecond
  apply G.reindex_congr
  exact conjLeftSecondNative_congr f k k' hk

theorem conjRLeftSecond_equation {Γ Θ Δ Λ I J : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P Γ (A :: Δ)) (g : G P Θ (B :: Λ)) (a : At Λ C) (h : G P I J) (z : At I C) :
    ofTerm (PositionalCut.cut (G.conjR (Δ := Δ) (Λ := Λ) f g)
      (At.shift (.conj A B :: Δ) a) h z).denote =
      ofTerm (conjRLeftSecond f a (PositionalCut.cut g a.there h z)).denote := by
  apply G.reindex_right_cancel_denote
    (congrArg (fun xs => J ++ xs) (At.erase_shift_at (.conj A B :: Δ) a))
  rw [PositionalCut.reindex_residues (G.conjR (Δ := Δ) (Λ := Λ) f g)
    (At.shift (.conj A B :: Δ) a) h z (At.erase_shift_at (.conj A B :: Δ) a) rfl]
  change ofTerm (G.cut ((LogicalDeletion.headShift (.conj A B :: Δ) a).right
    (G.conjR (Δ := Δ) (Λ := Λ) f g)) (z.toHead.left h)).denote =
      ofTerm (conjLeftSecondNative f (PositionalCut.cut g a.there h z)).denote
  apply (Rules.cut_congr (headShift_residual_conjR f g a) rfl).trans
  apply (conjLeftSecondNative_equation f ((a.toHead.consFixed B).right g) (z.toHead.left h)).trans
  exact conjLeftSecondNative_congr f _ _ (leftFirstChild_factor g a h z).symm

end BinaryLogical
namespace CutCommutation

theorem conjR_left_second_eliminated {Γ Θ Δ Λ I J : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P Γ (A :: Δ)) (g : G P Θ (B :: Λ)) (a : At Λ C) (h : G P I J) (z : At I C)
    (hf : f.CutFree) (af : f.Atomized) (hs : PositionalCut.Eliminated g a.there h z) :
    PositionalCut.Eliminated (G.conjR (Δ := Δ) (Λ := Λ) f g) (At.shift (.conj A B :: Δ) a) h z := by
  obtain ⟨k,hk,ak,ek⟩ := hs
  refine ⟨BinaryLogical.conjRLeftSecond f a k,?_,?_,?_⟩
  · change (BinaryLogical.conjRLeftSecond f a k).cutCount = 0
    rw [BinaryLogical.conjRLeftSecond_count]
    exact Nat.add_eq_zero_iff.mpr ⟨hf,hk⟩
  · exact (BinaryLogical.conjRLeftSecond_atomized f a k).mpr ⟨af,ak⟩
  · exact (BinaryLogical.conjRLeftSecond_congr f a k _ ek).trans
      (BinaryLogical.conjRLeftSecond_equation f g a h z).symm

theorem conjR_left_second_rank_step {Γ Θ Δ Λ I J : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P Γ (A :: Δ)) (g : G P Θ (B :: Λ)) (a : At Λ C) (h : G P I J) (z : At I C)
    (hc : PositionalCut.Clean (G.conjR (Δ := Δ) (Λ := Λ) f g) (At.shift (.conj A B :: Δ) a) h z)
    (ih : ∀ {K L M N : List (NormalForm P)} (b : G P K L) (v : At L C)
      (d : G P M N) (w : At M C),
      PositionalCut.rank b v d w < PositionalCut.rank (G.conjR (Δ := Δ) (Λ := Λ) f g)
        (At.shift (.conj A B :: Δ) a) h z →
      PositionalCut.Clean b v d w → PositionalCut.Eliminated b v d w) :
    PositionalCut.Eliminated (G.conjR (Δ := Δ) (Λ := Λ) f g) (At.shift (.conj A B :: Δ) a) h z := by
  have hd := PositionalCut.conjR_left_second_descent f g a h z hc
  exact conjR_left_second_eliminated f g a h z ((G.conjR_cutFree f g).mp hc.1).1 hc.2.2.1.1
    (ih g a.there h z hd.2 hd.1)

end CutCommutation
end DosenPetric.Reduced.Gentzen
