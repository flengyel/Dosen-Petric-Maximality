module

public import DosenPetric.GentzenBlockedConjBothEquation

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.BlockedConjBoth
universe u
variable {P : Type u}

theorem first_descent {A B : NormalForm P} {Γ Θ X Y Z T I J : List (NormalForm P)}
    (f : G P Γ (A::(X++.conj A B::Y))) (g : G P Θ (B::(Z++.conj A B::T)))
    (h : G P I J) (z : At I (.conj A B))
    (hc : PositionalCut.Clean (parent f g) (block A B X Y Z T).keep h z) :
    PositionalCut.Clean f (BlockedMix.firstTag (.conj A B) X Y).there h z ∧
      PositionalCut.rank f (BlockedMix.firstTag (.conj A B) X Y).there h z <
        PositionalCut.rank (parent f g) (block A B X Y Z T).keep h z := by
  have hd := (block A B X Y Z T).right_cut_descent (Nat.le_succ 2) (G.conjR f g)
    (((BlockedMix.firstTag (.conj A B) X Y).before (Z++.conj A B::T)).there) h z
    (by simpa only [Route.firstBlock_get,Route.secondBlock_get,At.shift] using first_get A B X Y Z T) hc
  have he := PositionalCut.conjR_left_first_descent f g (BlockedMix.firstTag (.conj A B) X Y) h z hd.1
  exact ⟨he.1,Nat.lt_trans he.2 hd.2⟩

theorem second_descent {A B : NormalForm P} {Γ Θ X Y Z T I J : List (NormalForm P)}
    (f : G P Γ (A::(X++.conj A B::Y))) (g : G P Θ (B::(Z++.conj A B::T)))
    (h : G P I J) (z : At I (.conj A B))
    (hc : PositionalCut.Clean (parent f g) (block A B X Y Z T).keep h z) :
    PositionalCut.Clean g (BlockedMix.firstTag (.conj A B) Z T).there h z ∧
      PositionalCut.rank g (BlockedMix.firstTag (.conj A B) Z T).there h z <
        PositionalCut.rank (parent f g) (block A B X Y Z T).keep h z := by
  have hd := (block A B X Y Z T).right_cut_descent (Nat.le_succ 2) (G.conjR f g)
    ((At.shift (X++.conj A B::Y) (BlockedMix.firstTag (.conj A B) Z T)).there) h z
    (by simpa only [Route.secondBlock_get,At.shift] using second_get A B X Y Z T) hc
  have he := PositionalCut.conjR_left_second_descent f g (BlockedMix.firstTag (.conj A B) Z T) h z hd.1
  exact ⟨he.1,Nat.lt_trans he.2 hd.2⟩

theorem contracted_rank_gt_one {A B : NormalForm P} {Γ Θ X Y Z T I J : List (NormalForm P)}
    (f : G P Γ (A::(X++.conj A B::Y))) (g : G P Θ (B::(Z++.conj A B::T)))
    (h : G P I J) (z : At I (.conj A B))
    (hc : PositionalCut.Clean (parent f g) (block A B X Y Z T).keep h z) :
    1 < (parent f g).rho .right (block A B X Y Z T).keep := by
  have hd := (first_descent f g h z hc).2
  have hp := f.rho_pos .right (BlockedMix.firstTag (.conj A B) X Y).there
  unfold PositionalCut.rank at hd
  omega

/-- Reuse the selected-child equation without a returned-rank bound. -/
theorem child_eliminated {Γ F I J : List (NormalForm P)} {A C : NormalForm P}
    (a : At F C) (f : G P Γ (A::F)) (h : G P I J) (z : At I C)
    (hf : PositionalCut.Eliminated f a.there h z) :
    ∃ k : G P (z.erase++Γ) (J++A::a.erase), k.CutFree ∧ k.Atomized ∧
      ofTerm k.denote = ofTerm (G.cut (SequentialConjBoth.child A C
        ((a.toHead.consFixed A).right f)) (z.toHead.left h)).denote := by
  obtain ⟨k,hk,ak,ek⟩ := hf
  exact ⟨k,hk,ak,ek.trans (BinaryLogical.leftFirstChild_factor f a h z)⟩

end DosenPetric.Reduced.Gentzen.BlockedConjBoth
