module

public import DosenPetric.GentzenBlockedConjSecondEquation

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.BlockedConjSecond
universe u
variable {P : Type u}

theorem original_descent {A B : NormalForm P} {Γ Θ F Z T I J : List (NormalForm P)}
    (f : G P Γ (A::F)) (g : G P Θ (B::(Z++.conj A B::T))) (h : G P I J) (z : At I (.conj A B))
    (hc : PositionalCut.Clean (parent f g) (block A B F Z T).keep h z) :
    PositionalCut.Clean g (parametric A B Z T).there h z ∧
      PositionalCut.rank g (parametric A B Z T).there h z <
        PositionalCut.rank (parent f g) (block A B F Z T).keep h z := by
  have hd := (block A B F Z T).right_cut_descent (Nat.le_refl 2) (G.conjR f g)
    ((At.shift F (parametric A B Z T)).there) h z (parametric_get A B F Z T) hc
  have he := PositionalCut.conjR_left_second_descent f g (parametric A B Z T) h z hd.1
  exact ⟨he.1,Nat.lt_trans he.2 hd.2⟩

theorem contracted_rank_gt_one {A B : NormalForm P} {Γ Θ F Z T I J : List (NormalForm P)}
    (f : G P Γ (A::F)) (g : G P Θ (B::(Z++.conj A B::T))) (h : G P I J) (z : At I (.conj A B))
    (hc : PositionalCut.Clean (parent f g) (block A B F Z T).keep h z) :
    1 < (parent f g).rho .right (block A B F Z T).keep := by
  have hd := (original_descent f g h z hc).2
  have hp := g.rho_pos .right (parametric A B Z T).there
  unfold PositionalCut.rank at hd
  omega

theorem first_cutFree_atomized {A B : NormalForm P} {Γ Θ F Z T I J : List (NormalForm P)}
    (f : G P Γ (A::F)) (g : G P Θ (B::(Z++.conj A B::T))) (h : G P I J) (z : At I (.conj A B))
    (hc : PositionalCut.Clean (parent f g) (block A B F Z T).keep h z) : f.CutFree ∧ f.Atomized := by
  have ht := hc.1
  change (parent f g).cutCount = 0 at ht
  rw [parent,ContractionBlock.countR,G.cutCount] at ht
  have af := ((block A B F Z T).atomizedR (Nat.le_refl 2) _ (G.conjR f g)).mp hc.2.2.1
  exact ⟨(Nat.add_eq_zero_iff.mp ht).1,af.1⟩

theorem native_child_eliminated {A B : NormalForm P} {Θ Z T I J : List (NormalForm P)}
    (g : G P Θ (B::(Z++.conj A B::T))) (h : G P I J) (z : At I (.conj A B))
    (hg : PositionalCut.Eliminated g (parametric A B Z T).there h z) :
    ∃ k : G P (z.erase++Θ) (J++B::(parametric A B Z T).erase), k.CutFree ∧ k.Atomized ∧
      ofTerm k.denote = ofTerm (G.cut
        (SequentialConjSecond.child (SequentialConjSecond.secondChild (parametric A B Z T) g))
        (z.toHead.left h)).denote := by
  obtain ⟨k,hk,ak,ek⟩ := hg
  exact ⟨k,hk,ak,ek.trans (BinaryLogical.leftFirstChild_factor g (parametric A B Z T) h z)⟩

end DosenPetric.Reduced.Gentzen.BlockedConjSecond
