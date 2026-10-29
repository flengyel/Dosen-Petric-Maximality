module

public import DosenPetric.GentzenDisjRightFirstEquation

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace DisjLogical

theorem input_first_disjL {F U Θ Δ Λ : List (NormalForm P)} {A B : NormalForm P}
    (p : StructuralProgram P F U) (f : G P (A :: U) Δ) (g : G P (B :: Θ) Λ) :
    ofTerm (((p.suffixFixed Θ).consFixed (.disj A B)).left (G.disjL f g)).denote =
      ofTerm (G.disjL ((p.consFixed A).left f) g).denote := by
  rw [StructuralProgram.left_denote,disjL_denote,disjL_denote,StructuralProgram.left_denote,
    BinaryLogical.structural_consFixed_arrow,BinaryLogical.structural_consFixed_arrow]
  have hs := p.suffixFixed_split .conj Θ
  dsimp only [side,sideM,conjMonoidal,category,split] at hs ⊢
  rw [← Laws.assoc (tensor .conj (id (.disj A B)) ((p.suffixFixed Θ).arrow .conj)),
    Laws.tensor_comp,Laws.id_comp,hs,tensor_factor .conj (id (.disj A B))]
  have hd := (disjPair_input_first (p.arrow .conj) (ofTerm f.denote) (ofTerm g.denote)).symm
  simp only [Laws.assoc]
  erw [← Laws.assoc (tensor .conj (id (.disj A B)) (tensor .conj (p.arrow .conj) (id (ante Θ)))),hd]

theorem headBefore_input_disjL {Γ Θ Δ Λ : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P (A :: Γ) Δ) (a : At Γ C) (g : G P (B :: Θ) Λ) :
    ofTerm (((LogicalDeletion.headBefore a Θ).consFixed (.disj A B)).left (G.disjL (Γ := Γ) (Θ := Θ) f g)).denote =
      ofTerm (G.disjL (Γ := C :: a.erase) (Θ := Θ) ((a.toHead.consFixed A).left f) g).denote := by
  rw [ExchangeScript.left_denote,ExchangeScript.consFixed_arrow,BinaryMix.headBefore_structural]
  have he := input_first_disjL a.toHead.structural f g
  rw [StructuralProgram.left_denote,BinaryLogical.structural_consFixed_arrow] at he
  dsimp only [side,sideM,conjMonoidal,category] at he ⊢
  change comp (tensor .conj (id (.disj A B)) ((a.toHead.structural.suffixFixed Θ).arrow .conj))
    (ofTerm (G.disjL (Γ := Γ) (Θ := Θ) f g).denote) = _
  rw [he]
  have ha : ofTerm ((a.toHead.structural.consFixed A).left f).denote =
      ofTerm ((a.toHead.consFixed A).left f).denote := by
    rw [StructuralProgram.left_denote,ExchangeScript.left_denote,BinaryLogical.structural_consFixed_arrow,
      ExchangeScript.consFixed_arrow,ExchangeScript.structural_arrow]
  exact Rules.disjLeft_congr ha rfl

theorem firstParent_factor {Γ Θ Δ Λ : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P (A :: Γ) Δ) (a : At Γ C) (g : G P (B :: Θ) Λ) :
    ofTerm ((((At.there (B := .disj A B) (a.before Θ)).toHead).reindex
      (congrArg (fun xs => C :: (.disj A B :: xs)) (a.erase_before Θ)) rfl).left (G.disjL (Γ := Γ) (Θ := Θ) f g)).denote =
      ofTerm ((HeadRouting.front [.disj A B] (a.erase ++ Θ) C).left
        (G.disjL (Γ := C :: a.erase) (Θ := Θ) ((a.toHead.consFixed A).left f) g)).denote := by
  have he := headBefore_input_disjL f a g
  rw [ExchangeScript.left_denote] at he
  rw [ExchangeScript.left_denote,BinaryLogical.headBefore_there_arrow,ExchangeScript.left_denote]
  change comp (comp ((HeadRouting.front [.disj A B] (a.erase ++ Θ) C).arrow .conj)
    (((LogicalDeletion.headBefore a Θ).consFixed (.disj A B)).arrow .conj)) (ofTerm (G.disjL (Γ := Γ) (Θ := Θ) f g).denote) = _
  rw [Laws.assoc,he]

theorem disjRightFirstNative_congr {Γ Θ Δ Λ I D : List (NormalForm P)} {A B : NormalForm P}
    (k k' : G P (A :: (Γ ++ I)) (Δ ++ D)) (g : G P (B :: Θ) Λ)
    (hk : ofTerm k.denote = ofTerm k'.denote) :
    ofTerm (disjRightFirstNative k g).denote = ofTerm (disjRightFirstNative k' g).denote := by
  unfold disjRightFirstNative
  rw [ExchangeScript.right_denote,ExchangeScript.left_denote,
    ExchangeScript.right_denote,ExchangeScript.left_denote]
  change comp (comp _ (ofTerm (Rules.disjLeft k.denote g.denote))) _ = _
  rw [Rules.disjLeft_congr hk rfl]
  rfl

def disjLRightFirst {Γ Θ Δ Λ I D : List (NormalForm P)} {A B C : NormalForm P}
    (a : At Γ C) (g : G P (B :: Θ) Λ) (k : G P (A :: (a.erase ++ I)) (Δ ++ D)) :
    G P ((At.there (B := .disj A B) (a.before Θ)).erase ++ I) ((Δ ++ Λ) ++ D) :=
  (disjRightFirstNative k g).reindex
    (congrArg (fun xs => (.disj A B :: xs) ++ I) (a.erase_before Θ)).symm rfl

theorem disjLRightFirst_count {Γ Θ Δ Λ I D : List (NormalForm P)} {A B C : NormalForm P}
    (a : At Γ C) (g : G P (B :: Θ) Λ) (k : G P (A :: (a.erase ++ I)) (Δ ++ D)) :
    (disjLRightFirst a g k).cutCount = k.cutCount + g.cutCount := by
  simp only [disjLRightFirst,disjRightFirstNative,G.count_reindex,
    ExchangeScript.right_count,ExchangeScript.left_count,G.cutCount]

theorem disjLRightFirst_atomized {Γ Θ Δ Λ I D : List (NormalForm P)} {A B C : NormalForm P}
    (a : At Γ C) (g : G P (B :: Θ) Λ) (k : G P (A :: (a.erase ++ I)) (Δ ++ D)) :
    (disjLRightFirst a g k).Atomized ↔ k.Atomized ∧ g.Atomized := by
  simp only [disjLRightFirst,disjRightFirstNative,G.atomized_reindex,
    ExchangeScript.right_atomized,ExchangeScript.left_atomized,G.Atomized]

theorem disjLRightFirst_congr {Γ Θ Δ Λ I D : List (NormalForm P)} {A B C : NormalForm P}
    (a : At Γ C) (g : G P (B :: Θ) Λ) (k k' : G P (A :: (a.erase ++ I)) (Δ ++ D))
    (hk : ofTerm k.denote = ofTerm k'.denote) :
    ofTerm (disjLRightFirst a g k).denote = ofTerm (disjLRightFirst a g k').denote := by
  unfold disjLRightFirst
  apply G.reindex_congr
  exact disjRightFirstNative_congr k k' g hk

theorem disjLRightFirst_equation {Γ Θ Δ Λ I J : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P (A :: Γ) Δ) (g : G P (B :: Θ) Λ) (h : G P I J) (z : At J C) (a : At Γ C) :
    ofTerm (PositionalCut.cut h z (G.disjL (Γ := Γ) (Θ := Θ) f g) (At.there (B := .disj A B) (a.before Θ))).denote =
      ofTerm (disjLRightFirst a g (PositionalCut.cut h z f a.there)).denote := by
  have hd : (At.there (B := .disj A B) (a.before Θ)).erase = .disj A B :: (a.erase ++ Θ) := by
    change .disj A B :: (a.before Θ).erase = .disj A B :: (a.erase ++ Θ)
    exact congrArg (List.cons (.disj A B)) (a.erase_before Θ)
  apply G.reindex_left_cancel_denote (congrArg (fun xs => xs ++ I) hd)
  rw [PositionalCut.reindex_residues h z (G.disjL (Γ := Γ) (Θ := Θ) f g) (At.there (B := .disj A B) (a.before Θ)) rfl hd]
  change ofTerm (G.cut (z.toHead.right h)
    ((((At.there (B := .disj A B) (a.before Θ)).toHead).reindex
      (congrArg (fun xs => C :: (.disj A B :: xs)) (a.erase_before Θ)) rfl).left (G.disjL (Γ := Γ) (Θ := Θ) f g))).denote =
      ofTerm (disjRightFirstNative (PositionalCut.cut h z f a.there) g).denote
  apply (Rules.cut_congr rfl (firstParent_factor f a g)).trans
  apply (disjRightFirstNative_equation ((a.toHead.consFixed A).left f) g (z.toHead.right h)).trans
  exact disjRightFirstNative_congr _ _ g (rightChild_factor h z f a).symm

end DisjLogical
namespace CutCommutation

theorem disjL_right_first_eliminated {Γ Θ Δ Λ I J : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P (A :: Γ) Δ) (g : G P (B :: Θ) Λ) (h : G P I J) (z : At J C) (a : At Γ C)
    (hg : g.CutFree) (ag : g.Atomized) (hs : PositionalCut.Eliminated h z f a.there) :
    PositionalCut.Eliminated h z (G.disjL (Γ := Γ) (Θ := Θ) f g) (At.there (B := .disj A B) (a.before Θ)) := by
  obtain ⟨k,hk,ak,ek⟩ := hs
  refine ⟨DisjLogical.disjLRightFirst a g k,?_,?_,?_⟩
  · change (DisjLogical.disjLRightFirst a g k).cutCount = 0
    rw [DisjLogical.disjLRightFirst_count]
    exact Nat.add_eq_zero_iff.mpr ⟨hk,hg⟩
  · exact (DisjLogical.disjLRightFirst_atomized a g k).mpr ⟨ak,ag⟩
  · exact (DisjLogical.disjLRightFirst_congr a g k _ ek).trans
      (DisjLogical.disjLRightFirst_equation f g h z a).symm

theorem disjL_right_first_rank_step {Γ Θ Δ Λ I J : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P (A :: Γ) Δ) (g : G P (B :: Θ) Λ) (h : G P I J) (z : At J C) (a : At Γ C)
    (hc : PositionalCut.Clean h z (G.disjL (Γ := Γ) (Θ := Θ) f g) (At.there (B := .disj A B) (a.before Θ)))
    (ih : ∀ {K L M N : List (NormalForm P)} (b : G P K L) (v : At L C)
      (d : G P M N) (w : At M C),
      PositionalCut.rank b v d w < PositionalCut.rank h z (G.disjL (Γ := Γ) (Θ := Θ) f g) (At.there (B := .disj A B) (a.before Θ)) →
      PositionalCut.Clean b v d w → PositionalCut.Eliminated b v d w) :
    PositionalCut.Eliminated h z (G.disjL (Γ := Γ) (Θ := Θ) f g) (At.there (B := .disj A B) (a.before Θ)) := by
  have hd := PositionalCut.disjL_right_first_descent f g h z a hc
  exact disjL_right_first_eliminated f g h z a ((G.disjL_cutFree f g).mp hc.2.1).2 hc.2.2.2.1.2
    (ih h z f a.there hd.2 hd.1)

end CutCommutation
end DosenPetric.Reduced.Gentzen
