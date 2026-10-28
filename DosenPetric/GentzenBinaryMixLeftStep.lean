module

public import DosenPetric.GentzenBinaryMixSymmetry

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace BinaryMix

/-- Rebuild the first mix branch using the actual swapped native rule and its
    unique-fiber residual program. All structural maps follow the child cut. -/
def firstRaw {Γ Θ Δ Λ T J : List (NormalForm P)} {C : NormalForm P}
    (a : At Δ C) (g : G P Θ Λ) (k : G P (T ++ Γ) (J ++ a.erase)) :
    G P (T ++ (Θ ++ Γ)) (J ++ (At.shift Λ a).erase) :=
  ((swapProgram Γ Θ).prefixFixed T).left
    ((((swapProgram Δ Λ).residual (At.shift Λ a) (a.before Λ) (swapProgram_single a)).prefixFixed J).right
      (leadingAt a g k))

theorem firstRaw_count {Γ Θ Δ Λ T J : List (NormalForm P)} {C : NormalForm P}
    (a : At Δ C) (g : G P Θ Λ) (k : G P (T ++ Γ) (J ++ a.erase)) :
    (firstRaw a g k).cutCount = k.cutCount + g.cutCount := by
  simp only [firstRaw,StructuralProgram.left_count,StructuralProgram.right_count,leadingAt_count]

theorem firstRaw_congr {Γ Θ Δ Λ T J : List (NormalForm P)} {C : NormalForm P}
    (a : At Δ C) (g : G P Θ Λ) (k k' : G P (T ++ Γ) (J ++ a.erase))
    (hk : ofTerm k.denote = ofTerm k'.denote) :
    ofTerm (firstRaw a g k).denote = ofTerm (firstRaw a g k').denote := by
  unfold firstRaw
  rw [StructuralProgram.left_denote,StructuralProgram.right_denote,
    StructuralProgram.left_denote,StructuralProgram.right_denote,leadingAt_congr a g k k' hk]

theorem first_equation {Γ Θ Δ Λ I J : List (NormalForm P)} {C : NormalForm P}
    (f : G P Γ Δ) (g : G P Θ Λ) (a : At Δ C) (h : G P I J) (z : At I C) :
    ofTerm (PositionalCut.cut (G.mix f g) (At.shift Λ a) h z).denote =
      ofTerm (firstRaw a g (PositionalCut.cut f a h z)).denote := by
  let p := swapProgram Δ Λ
  let q := swapProgram Γ Θ
  have he : ofTerm (G.mix f g).denote = ofTerm (q.left (p.right (G.mix g f))).denote := by
    rw [native_swap,ExchangeScript.left_denote,ExchangeScript.right_denote,
      StructuralProgram.left_denote,StructuralProgram.right_denote]
    simp only [p,q,swapProgram,ExchangeScript.structural_arrow]
  apply (PositionalCut.congr (At.shift Λ a) z he rfl).trans
  rw [CutCommutation.selected_opposite_left q]
  unfold firstRaw
  rw [StructuralProgram.left_denote,StructuralProgram.left_denote]
  rw [CutCommutation.same_right p (At.shift Λ a) (a.before Λ) (swapProgram_single a)]
  rw [StructuralProgram.right_denote,StructuralProgram.right_denote,leadingAt_equation f a g h z]

/-- Atomization is applied to the finished cut-free structural reconstruction. -/
def firstFinal {Γ Θ Δ Λ T J : List (NormalForm P)} {C : NormalForm P}
    (a : At Δ C) (g : G P Θ Λ) (k : G P (T ++ Γ) (J ++ a.erase)) :
    G P (T ++ (Θ ++ Γ)) (J ++ (At.shift Λ a).erase) := G.atomize (firstRaw a g k)

theorem firstFinal_atomized {Γ Θ Δ Λ T J : List (NormalForm P)} {C : NormalForm P}
    (a : At Δ C) (g : G P Θ Λ) (k : G P (T ++ Γ) (J ++ a.erase)) :
    (firstFinal a g k).Atomized := G.atomize_atomized _

end BinaryMix
namespace CutCommutation

theorem mix_left_first_eliminated {Γ Θ Δ Λ I J : List (NormalForm P)} {C : NormalForm P}
    (f : G P Γ Δ) (g : G P Θ Λ) (a : At Δ C) (h : G P I J) (z : At I C)
    (hg : g.CutFree) (hs : PositionalCut.Eliminated f a h z) :
    PositionalCut.Eliminated (G.mix f g) (At.shift Λ a) h z := by
  obtain ⟨k,hk,_,ek⟩ := hs
  have hc : (BinaryMix.firstRaw a g k).CutFree := by
    change (BinaryMix.firstRaw a g k).cutCount = 0
    rw [BinaryMix.firstRaw_count]
    exact Nat.add_eq_zero_iff.mpr ⟨hk,hg⟩
  refine ⟨BinaryMix.firstFinal a g k,G.atomize_cutFree _ hc,BinaryMix.firstFinal_atomized a g k,?_⟩
  exact (G.atomize_denote _).trans ((BinaryMix.firstRaw_congr a g k _ ek).trans
    (BinaryMix.first_equation f g a h z).symm)

theorem mix_left_first_rank_step {Γ Θ Δ Λ I J : List (NormalForm P)} {C : NormalForm P}
    (f : G P Γ Δ) (g : G P Θ Λ) (a : At Δ C) (h : G P I J) (z : At I C)
    (hc : PositionalCut.Clean (G.mix f g) (At.shift Λ a) h z)
    (ih : ∀ {K L M N : List (NormalForm P)} (b : G P K L) (v : At L C)
      (d : G P M N) (w : At M C),
      PositionalCut.rank b v d w < PositionalCut.rank (G.mix f g) (At.shift Λ a) h z →
      PositionalCut.Clean b v d w → PositionalCut.Eliminated b v d w) :
    PositionalCut.Eliminated (G.mix f g) (At.shift Λ a) h z := by
  have hd := PositionalCut.mix_left_first_descent f g a h z hc
  exact mix_left_first_eliminated f g a h z ((G.mix_cutFree f g).mp hc.1).2
    (ih f a h z hd.2 hd.1)

theorem mix_left_second_eliminated {Γ Θ Δ Λ I J : List (NormalForm P)} {C : NormalForm P}
    (f : G P Γ Δ) (g : G P Θ Λ) (a : At Λ C) (h : G P I J) (z : At I C)
    (hf : f.CutFree) (af : f.Atomized) (hs : PositionalCut.Eliminated g a h z) :
    PositionalCut.Eliminated (G.mix f g) (a.before Δ) h z := by
  obtain ⟨k,hk,ak,ek⟩ := hs
  refine ⟨BinaryMix.leadingAt a f k,?_,?_,?_⟩
  · change (BinaryMix.leadingAt a f k).cutCount = 0
    rw [BinaryMix.leadingAt_count]
    exact Nat.add_eq_zero_iff.mpr ⟨hk,hf⟩
  · exact (BinaryMix.leadingAt_atomized a f k).mpr ⟨ak,af⟩
  · exact (BinaryMix.leadingAt_congr a f k _ ek).trans
      (BinaryMix.leadingAt_equation g a f h z).symm

theorem mix_left_second_rank_step {Γ Θ Δ Λ I J : List (NormalForm P)} {C : NormalForm P}
    (f : G P Γ Δ) (g : G P Θ Λ) (a : At Λ C) (h : G P I J) (z : At I C)
    (hc : PositionalCut.Clean (G.mix f g) (a.before Δ) h z)
    (ih : ∀ {K L M N : List (NormalForm P)} (b : G P K L) (v : At L C)
      (d : G P M N) (w : At M C),
      PositionalCut.rank b v d w < PositionalCut.rank (G.mix f g) (a.before Δ) h z →
      PositionalCut.Clean b v d w → PositionalCut.Eliminated b v d w) :
    PositionalCut.Eliminated (G.mix f g) (a.before Δ) h z := by
  have hd := PositionalCut.mix_left_second_descent f g a h z hc
  exact mix_left_second_eliminated f g a h z ((G.mix_cutFree f g).mp hc.1).1 hc.2.2.1.1
    (ih g a h z hd.2 hd.1)

end CutCommutation
end DosenPetric.Reduced.Gentzen
