module

public import DosenPetric.GentzenBlockedConjFirstDescent

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace SequentialConjFirst

theorem fresh_cutFree_atomized {Γ Θ F U I J : List (NormalForm P)} {A B : NormalForm P}
    (k : G P (I++Γ) (J++A::F)) (g : G P Θ (B::U))
    (hk : k.CutFree) (ak : k.Atomized) (hg : g.CutFree) (ag : g.Atomized) :
    (fresh k g).CutFree ∧ (fresh k g).Atomized := by
  constructor
  · change (fresh k g).cutCount = 0
    simp only [fresh,G.cutCount,ExchangeScript.right_count]
    change k.cutCount = 0 at hk
    change g.cutCount = 0 at hg
    omega
  · simpa only [fresh,G.Atomized,ExchangeScript.right_atomized] using And.intro ak ag

theorem fresh_congr {Γ Θ F U I J : List (NormalForm P)} {A B : NormalForm P}
    (k k' : G P (I++Γ) (J++A::F)) (g : G P Θ (B::U))
    (he : ofTerm k.denote = ofTerm k'.denote) :
    ofTerm (fresh k g).denote = ofTerm (fresh k' g).denote := by
  apply Rules.conjRight_congr _ rfl
  simp only [ExchangeScript.right_denote,he]

end SequentialConjFirst
namespace BlockedConjFirst

theorem fresh_clean_and_rank {A B : NormalForm P} {Γ Θ X Y U I J : List (NormalForm P)}
    (f : G P Γ (A::(X++.conj A B::Y))) (g : G P Θ (B::U)) (h : G P I J) (z : At I (.conj A B))
    (hc : PositionalCut.Clean (parent f g) (block A B X Y U).keep h z)
    (k : G P (z.erase++Γ) (J++A::(parametric A B X Y).erase)) (hk : k.CutFree) (ak : k.Atomized) :
    PositionalCut.Clean (SequentialConjFirst.fresh k g) (.here (.conj A B) _) h z ∧
      PositionalCut.rank (SequentialConjFirst.fresh k g) (.here (.conj A B) _) h z <
        PositionalCut.rank (parent f g) (block A B X Y U).keep h z := by
  obtain ⟨hg,ag⟩ := second_cutFree_atomized f g h z hc
  have hf := SequentialConjFirst.fresh_cutFree_atomized k g hk ak hg ag
  refine ⟨⟨hf.1,hc.2.1,hf.2,hc.2.2.2.1,G.conjR_principal_blocked _ _,hc.2.2.2.2.2⟩,?_⟩
  exact PositionalCut.rank_fresh_conjR_lt (parent f g) _ h z (contracted_rank_gt_one f g h z hc) _ _

end BlockedConjFirst
namespace CutCommutation

theorem blockedR_conjunctionFirst_rank_step {A B : NormalForm P} {Γ Θ X Y U I J : List (NormalForm P)}
    (f : G P Γ (A::(X++.conj A B::Y))) (g : G P Θ (B::U)) (h : G P I J) (z : At I (.conj A B))
    (hc : PositionalCut.Clean (BlockedConjFirst.parent f g) (BlockedConjFirst.block A B X Y U).keep h z)
    (ih : ∀ {K L M N : List (NormalForm P)} (b : G P K L) (v : At L (.conj A B))
      (d : G P M N) (w : At M (.conj A B)),
      PositionalCut.rank b v d w <
        PositionalCut.rank (BlockedConjFirst.parent f g) (BlockedConjFirst.block A B X Y U).keep h z →
      PositionalCut.Clean b v d w → PositionalCut.Eliminated b v d w) :
    PositionalCut.Eliminated (BlockedConjFirst.parent f g) (BlockedConjFirst.block A B X Y U).keep h z := by
  have hd := BlockedConjFirst.original_descent f g h z hc
  have hs := ih f (BlockedConjFirst.parametric A B X Y).there h z hd.2 hd.1
  obtain ⟨k,hk,ak,ek⟩ := BlockedConjFirst.native_child_eliminated f h z hs
  have hf := BlockedConjFirst.fresh_clean_and_rank f g h z hc k hk ak
  obtain ⟨l,hl,_,el⟩ := ih (SequentialConjFirst.fresh k g) (.here (.conj A B) _) h z hf.2 hf.1
  let t := SequentialConjFirst.routed (.conj A B) (BlockedConjFirst.residue A B X Y U) l
  have ht : t.CutFree := by
    change t.cutCount = 0
    rw [SequentialConjFirst.routed_count]
    exact hl
  refine ⟨G.atomize t,G.atomize_cutFree t ht,G.atomize_atomized t,?_⟩
  apply (G.atomize_denote t).trans
  apply (SequentialConjFirst.routed_congr _ _ _ _ el).trans
  apply (SequentialConjFirst.routed_congr _ _ _ _ ?_).trans
  · exact (BlockedConjFirst.source_equation f g h z).symm
  · exact Rules.cut_congr (SequentialConjFirst.fresh_congr _ _ _ ek) (g:=(z.toHead.left h).denote) rfl

end CutCommutation
end DosenPetric.Reduced.Gentzen
