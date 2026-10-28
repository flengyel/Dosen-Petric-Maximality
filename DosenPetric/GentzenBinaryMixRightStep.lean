module

public import DosenPetric.GentzenBinaryMixRightSelected

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace BinaryMix

theorem swapProgram_single_shift {F U : List (NormalForm P)} {C : NormalForm P} (a : At U C) :
    (swapProgram F U).route.SingleFiber (a.before F) (At.shift F a) := by
  apply Route.singleFiber_of_unique
  · rw [StructuralProgram.route_get,swapProgram,ExchangeScript.structural_get,swapWhole_shift]
  · intro b hb
    rw [StructuralProgram.route_get,swapProgram,ExchangeScript.structural_get] at hb
    have he : (swapWhole F U).get b = (swapWhole F U).get (At.shift F a) := by
      rw [swapWhole_shift]
      exact hb
    exact (swapWhole F U).injective b (At.shift F a) he

def secondRaw {Γ Θ Δ Λ I D : List (NormalForm P)} {C : NormalForm P}
    (a : At Θ C) (f : G P Γ Δ) (k : G P (a.erase ++ I) (Λ ++ D)) :
    G P ((a.before Γ).erase ++ I) ((Λ ++ Δ) ++ D) :=
  (((swapProgram Γ Θ).residual (a.before Γ) (At.shift Γ a)
    (swapProgram_single_shift a)).suffixFixed I).left
      (((swapProgram Δ Λ).suffixFixed D).right (rightFirstAt a f k))

theorem secondRaw_count {Γ Θ Δ Λ I D : List (NormalForm P)} {C : NormalForm P}
    (a : At Θ C) (f : G P Γ Δ) (k : G P (a.erase ++ I) (Λ ++ D)) :
    (secondRaw a f k).cutCount = k.cutCount + f.cutCount := by
  simp only [secondRaw,StructuralProgram.left_count,StructuralProgram.right_count,rightFirstAt_count]

theorem secondRaw_congr {Γ Θ Δ Λ I D : List (NormalForm P)} {C : NormalForm P}
    (a : At Θ C) (f : G P Γ Δ) (k k' : G P (a.erase ++ I) (Λ ++ D))
    (hk : ofTerm k.denote = ofTerm k'.denote) :
    ofTerm (secondRaw a f k).denote = ofTerm (secondRaw a f k').denote := by
  unfold secondRaw
  rw [StructuralProgram.left_denote,StructuralProgram.right_denote,
    StructuralProgram.left_denote,StructuralProgram.right_denote,rightFirstAt_congr a f k k' hk]

theorem second_equation {Γ Θ Δ Λ I J : List (NormalForm P)} {C : NormalForm P}
    (f : G P Γ Δ) (g : G P Θ Λ) (h : G P I J) (z : At J C) (a : At Θ C) :
    ofTerm (PositionalCut.cut h z (G.mix f g) (a.before Γ)).denote =
      ofTerm (secondRaw a f (PositionalCut.cut h z g a)).denote := by
  let p := swapProgram Δ Λ
  let q := swapProgram Γ Θ
  have he : ofTerm (G.mix f g).denote = ofTerm (q.left (p.right (G.mix g f))).denote := by
    rw [native_swap,ExchangeScript.left_denote,ExchangeScript.right_denote,
      StructuralProgram.left_denote,StructuralProgram.right_denote]
    simp only [p,q,swapProgram,ExchangeScript.structural_arrow]
  apply (PositionalCut.congr z (a.before Γ) rfl he).trans
  rw [CutCommutation.same_left q (a.before Γ) (At.shift Γ a)
    (swapProgram_single_shift a) h z]
  unfold secondRaw
  rw [StructuralProgram.left_denote,StructuralProgram.left_denote]
  rw [CutCommutation.selected_opposite_right p]
  rw [StructuralProgram.right_denote,StructuralProgram.right_denote,rightFirstAt_equation g f h z a]

end BinaryMix
namespace CutCommutation

theorem mix_right_first_eliminated {Γ Θ Δ Λ I J : List (NormalForm P)} {C : NormalForm P}
    (f : G P Γ Δ) (g : G P Θ Λ) (h : G P I J) (z : At J C) (a : At Γ C)
    (hg : g.CutFree) (ag : g.Atomized) (hs : PositionalCut.Eliminated h z f a) :
    PositionalCut.Eliminated h z (G.mix f g) (At.shift Θ a) := by
  obtain ⟨k,hk,ak,ek⟩ := hs
  refine ⟨BinaryMix.rightFirstAt a g k,?_,?_,?_⟩
  · change (BinaryMix.rightFirstAt a g k).cutCount = 0
    rw [BinaryMix.rightFirstAt_count]
    exact Nat.add_eq_zero_iff.mpr ⟨hk,hg⟩
  · exact (BinaryMix.rightFirstAt_atomized a g k).mpr ⟨ak,ag⟩
  · exact (BinaryMix.rightFirstAt_congr a g k _ ek).trans
      (BinaryMix.rightFirstAt_equation f g h z a).symm

theorem mix_right_first_rank_step {Γ Θ Δ Λ I J : List (NormalForm P)} {C : NormalForm P}
    (f : G P Γ Δ) (g : G P Θ Λ) (h : G P I J) (z : At J C) (a : At Γ C)
    (hc : PositionalCut.Clean h z (G.mix f g) (At.shift Θ a))
    (ih : ∀ {K L M N : List (NormalForm P)} (b : G P K L) (v : At L C)
      (d : G P M N) (w : At M C),
      PositionalCut.rank b v d w < PositionalCut.rank h z (G.mix f g) (At.shift Θ a) →
      PositionalCut.Clean b v d w → PositionalCut.Eliminated b v d w) :
    PositionalCut.Eliminated h z (G.mix f g) (At.shift Θ a) := by
  have hd := PositionalCut.mix_right_first_descent f g h z a hc
  exact mix_right_first_eliminated f g h z a ((G.mix_cutFree f g).mp hc.2.1).2 hc.2.2.2.1.2
    (ih h z f a hd.2 hd.1)

theorem mix_right_second_eliminated {Γ Θ Δ Λ I J : List (NormalForm P)} {C : NormalForm P}
    (f : G P Γ Δ) (g : G P Θ Λ) (h : G P I J) (z : At J C) (a : At Θ C)
    (hf : f.CutFree) (hs : PositionalCut.Eliminated h z g a) :
    PositionalCut.Eliminated h z (G.mix f g) (a.before Γ) := by
  obtain ⟨k,hk,_,ek⟩ := hs
  have hc : (BinaryMix.secondRaw a f k).CutFree := by
    change (BinaryMix.secondRaw a f k).cutCount = 0
    rw [BinaryMix.secondRaw_count]
    exact Nat.add_eq_zero_iff.mpr ⟨hk,hf⟩
  refine ⟨G.atomize (BinaryMix.secondRaw a f k),G.atomize_cutFree _ hc,G.atomize_atomized _,?_⟩
  exact (G.atomize_denote _).trans ((BinaryMix.secondRaw_congr a f k _ ek).trans
    (BinaryMix.second_equation f g h z a).symm)

theorem mix_right_second_rank_step {Γ Θ Δ Λ I J : List (NormalForm P)} {C : NormalForm P}
    (f : G P Γ Δ) (g : G P Θ Λ) (h : G P I J) (z : At J C) (a : At Θ C)
    (hc : PositionalCut.Clean h z (G.mix f g) (a.before Γ))
    (ih : ∀ {K L M N : List (NormalForm P)} (b : G P K L) (v : At L C)
      (d : G P M N) (w : At M C),
      PositionalCut.rank b v d w < PositionalCut.rank h z (G.mix f g) (a.before Γ) →
      PositionalCut.Clean b v d w → PositionalCut.Eliminated b v d w) :
    PositionalCut.Eliminated h z (G.mix f g) (a.before Γ) := by
  have hd := PositionalCut.mix_right_second_descent f g h z a hc
  exact mix_right_second_eliminated f g h z a ((G.mix_cutFree f g).mp hc.2.1).1
    (ih h z g a hd.2 hd.1)

end CutCommutation
end DosenPetric.Reduced.Gentzen
