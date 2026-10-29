module

public import DosenPetric.GentzenBlockedConjFirstRank
public import DosenPetric.GentzenConjSecondSelected

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.SequentialConjSecond
universe u
variable {P : Type u}

def body {Γ Θ F U : List (NormalForm P)} {A B : NormalForm P}
    (f : G P Γ (A::F)) (g : G P Θ (B::.conj A B::U)) :
    G P (Γ++Θ) (.conj A B::.conj A B::(F++U)) :=
  (HeadRouting.front (.conj A B::F) U (.conj A B)).right
    (G.conjR (Δ:=F) (Λ:=.conj A B::U) f g)

def parent {Γ Θ F U : List (NormalForm P)} {A B : NormalForm P}
    (f : G P Γ (A::F)) (g : G P Θ (B::.conj A B::U)) :
    G P (Γ++Θ) (.conj A B::(F++U)) := SequentialRepair.headParentRight (body f g)

def child {Θ U : List (NormalForm P)} {A B : NormalForm P}
    (g : G P Θ (B::.conj A B::U)) : G P Θ (.conj A B::B::U) :=
  (HeadRouting.front [B] U (.conj A B)).right g

def fresh {Γ Θ F U I J : List (NormalForm P)} {A B : NormalForm P}
    (f : G P Γ (A::F)) (k : G P (I++Θ) (J++B::U)) :
    G P (Γ++(I++Θ)) (.conj A B::(F++(J++U))) :=
  G.conjR f ((HeadRouting.front J U B).right k)

def adapted {Γ Θ F U I J : List (NormalForm P)} {A B : NormalForm P}
    (f : G P Γ (A::F)) (k : G P (I++Θ) (J++B::U)) :
    G P (I++(Γ++Θ)) (.conj A B::(J++(F++U))) :=
  ((BinaryMix.swapBlocks F J U).consFixed (.conj A B)).structural.right
    ((BinaryMix.swapBlocks Γ I Θ).structural.left (fresh f k))

theorem first_equation {Γ Θ F U I J : List (NormalForm P)} {A B : NormalForm P}
    (f : G P Γ (A::F)) (g : G P Θ (B::.conj A B::U)) (h : G P (.conj A B::I) J) :
    ofTerm ((HeadRouting.front J (F++U) (.conj A B)).right (G.cut (body f g) h)).denote =
      ofTerm (adapted f (G.cut (child g) h)).denote := by
  have he := BinaryLogical.conjLeftSecondNative_equation f g h
  rw [ExchangeScript.right_denote,body,he,BinaryLogical.conjLeftSecondNative,ExchangeScript.right_denote]
  have hc := (HeadRouting.front J (F++U) (.conj A B)).arrow_inverse .disj
  change comp ((HeadRouting.front J (F++U) (.conj A B)).inverse.arrow .disj)
    ((HeadRouting.front J (F++U) (.conj A B)).arrow .disj) = id _ at hc
  rw [Laws.assoc]
  erw [hc]
  erw [Laws.comp_id]
  simp only [adapted,fresh,ExchangeScript.structural_left,ExchangeScript.structural_right]
  rfl

def rebuild {Γ Θ F U I J : List (NormalForm P)} (C : NormalForm P)
    (l : G P (I++(Γ++(I++Θ))) (J++(F++(J++U)))) : G P (I++(Γ++Θ)) (J++(F++U)) :=
  SequentialRepair.prefixRepair
    (SequentialAdapters.rightResult (BinaryMix.swapBlocks Γ I Θ).structural
      ((BinaryMix.swapBlocks F J U).consFixed C).structural
      (.here C (J++(F++U))) (.here C (F++(J++U)))
      (ExchangeScript.structural_singleFiber _ _ _ (ExchangeScript.consFixed_here C _)) l)

theorem native_equation {Γ Θ F U I J : List (NormalForm P)} {A B : NormalForm P}
    (f : G P Γ (A::F)) (g : G P Θ (B::.conj A B::U)) (h : G P (.conj A B::I) J) :
    ofTerm (G.cut (parent f g) h).denote =
      ofTerm (rebuild (.conj A B) (G.cut (fresh f (G.cut (child g) h)) h)).denote := by
  apply (SequentialRepair.headParentRight_equation (body f g) h).trans
  have he : ofTerm (SequentialRepair.rightTwoCuts (body f g) h).denote =
      ofTerm (G.cut (adapted f (G.cut (child g) h)) h).denote :=
    Rules.cut_congr (first_equation f g h) (g:=h.denote) rfl
  apply (SequentialRepair.prefixRepair_congr _ _ he).trans
  apply SequentialRepair.prefixRepair_congr
  have he := SequentialAdapters.right_equation (BinaryMix.swapBlocks Γ I Θ).structural
    ((BinaryMix.swapBlocks F J U).consFixed (.conj A B)).structural _ _
    (ExchangeScript.structural_singleFiber _ _ _ (ExchangeScript.consFixed_here (.conj A B) _))
    (fresh f (G.cut (child g) h)) h (.here (.conj A B) I)
  simp only [PositionalCut.head] at he
  exact he

end DosenPetric.Reduced.Gentzen.SequentialConjSecond
