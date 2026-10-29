module

public import DosenPetric.GentzenBlockedConjFirstEquation

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.BlockedConjFirst
universe u
variable {P : Type u}

theorem original_descent {A B : NormalForm P} {Γ Θ X Y U I J : List (NormalForm P)}
    (f : G P Γ (A::(X++.conj A B::Y))) (g : G P Θ (B::U)) (h : G P I J) (z : At I (.conj A B))
    (hc : PositionalCut.Clean (parent f g) (block A B X Y U).keep h z) :
    PositionalCut.Clean f (parametric A B X Y).there h z ∧
      PositionalCut.rank f (parametric A B X Y).there h z <
        PositionalCut.rank (parent f g) (block A B X Y U).keep h z := by
  have hd := (block A B X Y U).right_cut_descent (Nat.le_refl 2) (G.conjR f g)
    (((parametric A B X Y).before U).there) h z (parametric_get A B X Y U) hc
  have he := PositionalCut.conjR_left_first_descent f g (parametric A B X Y) h z hd.1
  exact ⟨he.1,Nat.lt_trans he.2 hd.2⟩

theorem contracted_rank_gt_one {A B : NormalForm P} {Γ Θ X Y U I J : List (NormalForm P)}
    (f : G P Γ (A::(X++.conj A B::Y))) (g : G P Θ (B::U)) (h : G P I J) (z : At I (.conj A B))
    (hc : PositionalCut.Clean (parent f g) (block A B X Y U).keep h z) :
    1 < (parent f g).rho .right (block A B X Y U).keep := by
  have hd := (original_descent f g h z hc).2
  have hp := f.rho_pos .right (parametric A B X Y).there
  unfold PositionalCut.rank at hd
  omega

theorem second_cutFree_atomized {A B : NormalForm P} {Γ Θ X Y U I J : List (NormalForm P)}
    (f : G P Γ (A::(X++.conj A B::Y))) (g : G P Θ (B::U)) (h : G P I J) (z : At I (.conj A B))
    (hc : PositionalCut.Clean (parent f g) (block A B X Y U).keep h z) : g.CutFree ∧ g.Atomized := by
  have ht := hc.1
  change (parent f g).cutCount = 0 at ht
  rw [parent,ContractionBlock.countR,G.cutCount] at ht
  have ag := ((block A B X Y U).atomizedR (Nat.le_refl 2) _ (G.conjR f g)).mp hc.2.2.1
  exact ⟨(Nat.add_eq_zero_iff.mp ht).2,ag.2⟩

theorem native_child_eliminated {A B : NormalForm P} {Γ X Y I J : List (NormalForm P)}
    (f : G P Γ (A::(X++.conj A B::Y))) (h : G P I J) (z : At I (.conj A B))
    (hf : PositionalCut.Eliminated f (parametric A B X Y).there h z) :
    ∃ k : G P (z.erase++Γ) (J++A::(parametric A B X Y).erase), k.CutFree ∧ k.Atomized ∧
      ofTerm k.denote = ofTerm (G.cut
        (SequentialConjFirst.child (SequentialConjFirst.firstChild (parametric A B X Y) f))
        (z.toHead.left h)).denote := by
  obtain ⟨k,hk,ak,ek⟩ := hf
  exact ⟨k,hk,ak,ek.trans (BinaryLogical.leftFirstChild_factor f (parametric A B X Y) h z)⟩

end DosenPetric.Reduced.Gentzen.BlockedConjFirst
