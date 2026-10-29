module

public import DosenPetric.GentzenBlockedConjSecondDescent

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace SequentialConjSecond

theorem fresh_cutFree_atomized {Γ Θ F U I J : List (NormalForm P)} {A B : NormalForm P}
    (f : G P Γ (A::F)) (k : G P (I++Θ) (J++B::U))
    (hf : f.CutFree) (af : f.Atomized) (hk : k.CutFree) (ak : k.Atomized) :
    (fresh f k).CutFree ∧ (fresh f k).Atomized := by
  constructor
  · change (fresh f k).cutCount = 0
    simp only [fresh,G.cutCount,ExchangeScript.right_count]
    change k.cutCount = 0 at hk
    change f.cutCount = 0 at hf
    omega
  · simpa only [fresh,G.Atomized,ExchangeScript.right_atomized] using And.intro af ak

theorem fresh_congr {Γ Θ F U I J : List (NormalForm P)} {A B : NormalForm P}
    (f : G P Γ (A::F)) (k k' : G P (I++Θ) (J++B::U))
    (he : ofTerm k.denote = ofTerm k'.denote) :
    ofTerm (fresh f k).denote = ofTerm (fresh f k').denote := by
  apply Rules.conjRight_congr rfl
  simp only [ExchangeScript.right_denote,he]

end SequentialConjSecond
namespace BlockedConjSecond

theorem fresh_clean_and_rank {A B : NormalForm P} {Γ Θ F Z T I J : List (NormalForm P)}
    (f : G P Γ (A::F)) (g : G P Θ (B::(Z++.conj A B::T))) (h : G P I J) (z : At I (.conj A B))
    (hc : PositionalCut.Clean (parent f g) (block A B F Z T).keep h z)
    (k : G P (z.erase++Θ) (J++B::(parametric A B Z T).erase)) (hk : k.CutFree) (ak : k.Atomized) :
    PositionalCut.Clean (SequentialConjSecond.fresh f k) (.here (.conj A B) _) h z ∧
      PositionalCut.rank (SequentialConjSecond.fresh f k) (.here (.conj A B) _) h z <
        PositionalCut.rank (parent f g) (block A B F Z T).keep h z := by
  obtain ⟨hf,af⟩ := first_cutFree_atomized f g h z hc
  have ht := SequentialConjSecond.fresh_cutFree_atomized f k hf af hk ak
  refine ⟨⟨ht.1,hc.2.1,ht.2,hc.2.2.2.1,G.conjR_principal_blocked _ _,hc.2.2.2.2.2⟩,?_⟩
  exact PositionalCut.rank_fresh_conjR_lt (parent f g) _ h z (contracted_rank_gt_one f g h z hc) _ _

end BlockedConjSecond
namespace CutCommutation

theorem blockedR_conjunctionSecond_rank_step {A B : NormalForm P} {Γ Θ F Z T I J : List (NormalForm P)}
    (f : G P Γ (A::F)) (g : G P Θ (B::(Z++.conj A B::T))) (h : G P I J) (z : At I (.conj A B))
    (hc : PositionalCut.Clean (BlockedConjSecond.parent f g) (BlockedConjSecond.block A B F Z T).keep h z)
    (ih : ∀ {K L M N : List (NormalForm P)} (b : G P K L) (v : At L (.conj A B))
      (d : G P M N) (w : At M (.conj A B)),
      PositionalCut.rank b v d w <
        PositionalCut.rank (BlockedConjSecond.parent f g) (BlockedConjSecond.block A B F Z T).keep h z →
      PositionalCut.Clean b v d w → PositionalCut.Eliminated b v d w) :
    PositionalCut.Eliminated (BlockedConjSecond.parent f g) (BlockedConjSecond.block A B F Z T).keep h z := by
  have hd := BlockedConjSecond.original_descent f g h z hc
  have hs := ih g (BlockedConjSecond.parametric A B Z T).there h z hd.2 hd.1
  obtain ⟨k,hk,ak,ek⟩ := BlockedConjSecond.native_child_eliminated g h z hs
  have hf := BlockedConjSecond.fresh_clean_and_rank f g h z hc k hk ak
  obtain ⟨l,hl,_,el⟩ := ih (SequentialConjSecond.fresh f k) (.here (.conj A B) _) h z hf.2 hf.1
  let t := SequentialConjSecond.routed (.conj A B) (BlockedConjSecond.residue A B F Z T) l
  have ht : t.CutFree := by
    change t.cutCount = 0
    rw [SequentialConjSecond.routed_count]
    exact hl
  refine ⟨G.atomize t,G.atomize_cutFree t ht,G.atomize_atomized t,?_⟩
  apply (G.atomize_denote t).trans
  apply (SequentialConjSecond.routed_congr _ _ _ _ el).trans
  apply (SequentialConjSecond.routed_congr _ _ _ _ ?_).trans
  · exact (BlockedConjSecond.source_equation f g h z).symm
  · exact Rules.cut_congr (SequentialConjSecond.fresh_congr _ _ _ ek) (g:=(z.toHead.left h).denote) rfl

end CutCommutation
end DosenPetric.Reduced.Gentzen
