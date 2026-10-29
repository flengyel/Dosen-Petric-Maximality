module

public import DosenPetric.GentzenConjLeftNativeLaws

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace BinaryLogical

theorem leftFirstParent_factor {Γ Θ Δ Λ : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P Γ (A :: Δ)) (a : At Δ C) (g : G P Θ (B :: Λ)) :
    ofTerm ((((At.there (B := .conj A B) (a.before Λ)).toHead).reindex
      (congrArg (fun xs => C :: (.conj A B :: xs)) (a.erase_before Λ)) rfl).right (G.conjR (Δ := Δ) (Λ := Λ) f g)).denote =
      ofTerm ((HeadRouting.front [.conj A B] (a.erase ++ Λ) C).right
        (G.conjR (Δ := C :: a.erase) (Λ := Λ) ((a.toHead.consFixed A).right f) g)).denote := by
  have he := headBefore_residual_conjR f a g
  rw [ExchangeScript.right_denote] at he
  rw [ExchangeScript.right_denote,headBefore_there_arrow,ExchangeScript.right_denote]
  change comp (ofTerm (G.conjR (Δ := Δ) (Λ := Λ) f g).denote)
    (comp (((LogicalDeletion.headBefore a Λ).consFixed (.conj A B)).arrow .disj)
      ((HeadRouting.front [.conj A B] (a.erase ++ Λ) C).arrow .disj)) = _
  erw [← Laws.assoc,he]

def conjRLeftFirst {Γ Θ Δ Λ T J : List (NormalForm P)} {A B C : NormalForm P}
    (a : At Δ C) (g : G P Θ (B :: Λ)) (k : G P (T ++ Γ) (J ++ (A :: a.erase))) :
    G P (T ++ (Γ ++ Θ)) (J ++ (At.there (B := .conj A B) (a.before Λ)).erase) :=
  (conjLeftFirstNative k g).reindex rfl
    (congrArg (fun xs => J ++ (.conj A B :: xs)) (a.erase_before Λ)).symm

theorem conjRLeftFirst_count {Γ Θ Δ Λ T J : List (NormalForm P)} {A B C : NormalForm P}
    (a : At Δ C) (g : G P Θ (B :: Λ)) (k : G P (T ++ Γ) (J ++ (A :: a.erase))) :
    (conjRLeftFirst a g k).cutCount = k.cutCount + g.cutCount := by
  rw [conjRLeftFirst,G.count_reindex,conjLeftFirstNative_count]

theorem conjRLeftFirst_atomized {Γ Θ Δ Λ T J : List (NormalForm P)} {A B C : NormalForm P}
    (a : At Δ C) (g : G P Θ (B :: Λ)) (k : G P (T ++ Γ) (J ++ (A :: a.erase))) :
    (conjRLeftFirst a g k).Atomized ↔ k.Atomized ∧ g.Atomized := by
  rw [conjRLeftFirst,G.atomized_reindex,conjLeftFirstNative_atomized]

theorem conjRLeftFirst_congr {Γ Θ Δ Λ T J : List (NormalForm P)} {A B C : NormalForm P}
    (a : At Δ C) (g : G P Θ (B :: Λ)) (k k' : G P (T ++ Γ) (J ++ (A :: a.erase)))
    (hk : ofTerm k.denote = ofTerm k'.denote) :
    ofTerm (conjRLeftFirst a g k).denote = ofTerm (conjRLeftFirst a g k').denote := by
  unfold conjRLeftFirst
  apply G.reindex_congr
  exact conjLeftFirstNative_congr k k' g hk

theorem conjRLeftFirst_equation {Γ Θ Δ Λ I J : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P Γ (A :: Δ)) (g : G P Θ (B :: Λ)) (a : At Δ C) (h : G P I J) (z : At I C) :
    ofTerm (PositionalCut.cut (G.conjR (Δ := Δ) (Λ := Λ) f g) (At.there (B := .conj A B) (a.before Λ)) h z).denote =
      ofTerm (conjRLeftFirst a g (PositionalCut.cut f a.there h z)).denote := by
  have hd : (At.there (B := .conj A B) (a.before Λ)).erase =
      .conj A B :: (a.erase ++ Λ) := by
    change .conj A B :: (a.before Λ).erase = .conj A B :: (a.erase ++ Λ)
    exact congrArg (List.cons (.conj A B)) (a.erase_before Λ)
  apply G.reindex_right_cancel_denote
    (congrArg (fun xs => J ++ xs) hd)
  rw [PositionalCut.reindex_residues (G.conjR (Δ := Δ) (Λ := Λ) f g) (At.there (B := .conj A B) (a.before Λ)) h z
    hd rfl]
  change ofTerm (G.cut ((((At.there (B := .conj A B) (a.before Λ)).toHead).reindex
      (congrArg (fun xs => C :: (.conj A B :: xs)) (a.erase_before Λ)) rfl).right (G.conjR (Δ := Δ) (Λ := Λ) f g))
        (z.toHead.left h)).denote =
    ofTerm (conjLeftFirstNative (PositionalCut.cut f a.there h z) g).denote
  apply (Rules.cut_congr (leftFirstParent_factor f a g) rfl).trans
  apply (conjLeftFirstNative_equation ((a.toHead.consFixed A).right f) g (z.toHead.left h)).trans
  exact conjLeftFirstNative_congr _ _ g (leftFirstChild_factor f a h z).symm

end BinaryLogical
namespace CutCommutation

theorem conjR_left_first_eliminated {Γ Θ Δ Λ I J : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P Γ (A :: Δ)) (g : G P Θ (B :: Λ)) (a : At Δ C) (h : G P I J) (z : At I C)
    (hg : g.CutFree) (ag : g.Atomized) (hs : PositionalCut.Eliminated f a.there h z) :
    PositionalCut.Eliminated (G.conjR (Δ := Δ) (Λ := Λ) f g) (At.there (B := .conj A B) (a.before Λ)) h z := by
  obtain ⟨k,hk,ak,ek⟩ := hs
  refine ⟨BinaryLogical.conjRLeftFirst a g k,?_,?_,?_⟩
  · change (BinaryLogical.conjRLeftFirst a g k).cutCount = 0
    rw [BinaryLogical.conjRLeftFirst_count]
    exact Nat.add_eq_zero_iff.mpr ⟨hk,hg⟩
  · exact (BinaryLogical.conjRLeftFirst_atomized a g k).mpr ⟨ak,ag⟩
  · exact (BinaryLogical.conjRLeftFirst_congr a g k _ ek).trans
      (BinaryLogical.conjRLeftFirst_equation f g a h z).symm

theorem conjR_left_first_rank_step {Γ Θ Δ Λ I J : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P Γ (A :: Δ)) (g : G P Θ (B :: Λ)) (a : At Δ C) (h : G P I J) (z : At I C)
    (hc : PositionalCut.Clean (G.conjR (Δ := Δ) (Λ := Λ) f g) (At.there (B := .conj A B) (a.before Λ)) h z)
    (ih : ∀ {K L M N : List (NormalForm P)} (b : G P K L) (v : At L C)
      (d : G P M N) (w : At M C),
      PositionalCut.rank b v d w < PositionalCut.rank (G.conjR (Δ := Δ) (Λ := Λ) f g) (At.there (B := .conj A B) (a.before Λ)) h z →
      PositionalCut.Clean b v d w → PositionalCut.Eliminated b v d w) :
    PositionalCut.Eliminated (G.conjR (Δ := Δ) (Λ := Λ) f g) (At.there (B := .conj A B) (a.before Λ)) h z := by
  have hd := PositionalCut.conjR_left_first_descent f g a h z hc
  exact conjR_left_first_eliminated f g a h z ((G.conjR_cutFree f g).mp hc.1).2 hc.2.2.1.2
    (ih f a.there h z hd.2 hd.1)

end CutCommutation
end DosenPetric.Reduced.Gentzen
