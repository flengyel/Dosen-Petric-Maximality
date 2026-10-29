module

public import DosenPetric.GentzenBlockedConjBothDescent

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace SequentialConjBoth

theorem fresh_cutFree_atomized {Γ Θ D E I J : List (NormalForm P)} {A B : NormalForm P}
    (k : G P (I++Γ) (J++A::D)) (l : G P (I++Θ) (J++B::E))
    (hk : k.CutFree) (ak : k.Atomized) (hl : l.CutFree) (al : l.Atomized) :
    (fresh k l).CutFree ∧ (fresh k l).Atomized := by
  constructor
  · change (fresh k l).cutCount = 0
    simp only [fresh,G.cutCount,ExchangeScript.right_count]
    change k.cutCount = 0 at hk
    change l.cutCount = 0 at hl
    omega
  · simpa only [fresh,G.Atomized,ExchangeScript.right_atomized] using And.intro ak al

theorem fresh_congr {Γ Θ D E I J : List (NormalForm P)} {A B : NormalForm P}
    (k k' : G P (I++Γ) (J++A::D)) (l l' : G P (I++Θ) (J++B::E))
    (ek : ofTerm k.denote = ofTerm k'.denote) (el : ofTerm l.denote = ofTerm l'.denote) :
    ofTerm (fresh k l).denote = ofTerm (fresh k' l').denote := by
  apply Rules.conjRight_congr
  · simp only [ExchangeScript.right_denote,ek]
  · simp only [ExchangeScript.right_denote,el]

end SequentialConjBoth
namespace BlockedConjBoth

theorem fresh_clean_and_rank {A B : NormalForm P} {Γ Θ X Y Z T I J : List (NormalForm P)}
    (f : G P Γ (A::(X++.conj A B::Y))) (g : G P Θ (B::(Z++.conj A B::T)))
    (h : G P I J) (z : At I (.conj A B))
    (hc : PositionalCut.Clean (parent f g) (block A B X Y Z T).keep h z)
    (k : G P (z.erase++Γ) (J++A::(BlockedMix.firstTag (.conj A B) X Y).erase))
    (l : G P (z.erase++Θ) (J++B::(BlockedMix.firstTag (.conj A B) Z T).erase))
    (hk : k.CutFree) (ak : k.Atomized) (hl : l.CutFree) (al : l.Atomized) :
    PositionalCut.Clean (SequentialConjBoth.fresh k l) (.here (.conj A B) _) h z ∧
      PositionalCut.rank (SequentialConjBoth.fresh k l) (.here (.conj A B) _) h z <
        PositionalCut.rank (parent f g) (block A B X Y Z T).keep h z := by
  have hf := SequentialConjBoth.fresh_cutFree_atomized k l hk ak hl al
  refine ⟨⟨hf.1,hc.2.1,hf.2,hc.2.2.2.1,G.conjR_principal_blocked _ _,hc.2.2.2.2.2⟩,?_⟩
  exact PositionalCut.rank_fresh_conjR_lt (parent f g) _ h z (contracted_rank_gt_one f g h z hc) _ _

end BlockedConjBoth
namespace CutCommutation

theorem blockedR_conjunctionBoth_rank_step {A B : NormalForm P} {Γ Θ X Y Z T I J : List (NormalForm P)}
    (f : G P Γ (A::(X++.conj A B::Y))) (g : G P Θ (B::(Z++.conj A B::T)))
    (h : G P I J) (z : At I (.conj A B))
    (hc : PositionalCut.Clean (BlockedConjBoth.parent f g) (BlockedConjBoth.block A B X Y Z T).keep h z)
    (ih : ∀ {K L M N : List (NormalForm P)} (b : G P K L) (v : At L (.conj A B))
      (d : G P M N) (w : At M (.conj A B)),
      PositionalCut.rank b v d w <
        PositionalCut.rank (BlockedConjBoth.parent f g) (BlockedConjBoth.block A B X Y Z T).keep h z →
      PositionalCut.Clean b v d w → PositionalCut.Eliminated b v d w) :
    PositionalCut.Eliminated (BlockedConjBoth.parent f g) (BlockedConjBoth.block A B X Y Z T).keep h z := by
  have hd := BlockedConjBoth.first_descent f g h z hc
  have he := BlockedConjBoth.second_descent f g h z hc
  have hs := ih f (BlockedMix.firstTag (.conj A B) X Y).there h z hd.2 hd.1
  have ht := ih g (BlockedMix.firstTag (.conj A B) Z T).there h z he.2 he.1
  obtain ⟨k,hk,ak,ek⟩ := BlockedConjBoth.child_eliminated (BlockedMix.firstTag (.conj A B) X Y) f h z hs
  obtain ⟨l,hl,al,el⟩ := BlockedConjBoth.child_eliminated (BlockedMix.firstTag (.conj A B) Z T) g h z ht
  have hf := BlockedConjBoth.fresh_clean_and_rank f g h z hc k l hk ak hl al
  obtain ⟨m,hm,_,em⟩ := ih (SequentialConjBoth.fresh k l) (.here (.conj A B) _) h z hf.2 hf.1
  let t := SequentialConjBoth.rebuild (.conj A B) (BlockedConjBoth.firstResidue A B X Y Z T)
    (BlockedConjBoth.secondResidue A B X Y Z T) m
  have hc' : t.CutFree := by
    change t.cutCount = 0
    rw [SequentialConjBoth.rebuild_count]
    exact hm
  refine ⟨G.atomize t,G.atomize_cutFree t hc',G.atomize_atomized t,?_⟩
  apply (G.atomize_denote t).trans
  apply (SequentialConjBoth.rebuild_congr _ _ _ _ _ em).trans
  apply (SequentialConjBoth.rebuild_congr _ _ _ _ _ ?_).trans
  · exact (BlockedConjBoth.source_equation f g h z).symm
  · exact Rules.cut_congr (SequentialConjBoth.fresh_congr _ _ _ _ ek el) (g:=(z.toHead.left h).denote) rfl

end CutCommutation
end DosenPetric.Reduced.Gentzen
