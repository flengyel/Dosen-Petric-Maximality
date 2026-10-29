module

public import DosenPetric.GentzenSequentialRightAdapters
public import DosenPetric.GentzenConjLeftSelected

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.SequentialConjFirst
universe u
variable {P : Type u}

def body {Γ Θ F U : List (NormalForm P)} {A B : NormalForm P}
    (f : G P Γ (A::.conj A B::F)) (g : G P Θ (B::U)) :
    G P (Γ++Θ) (.conj A B::.conj A B::(F++U)) :=
  (HeadRouting.front [.conj A B] (F++U) (.conj A B)).right (G.conjR (Δ:=.conj A B::F) (Λ:=U) f g)

def parent {Γ Θ F U : List (NormalForm P)} {A B : NormalForm P}
    (f : G P Γ (A::.conj A B::F)) (g : G P Θ (B::U)) :
    G P (Γ++Θ) (.conj A B::(F++U)) := SequentialRepair.headParentRight (body f g)

def child {Γ F : List (NormalForm P)} {A B : NormalForm P}
    (f : G P Γ (A::.conj A B::F)) : G P Γ (.conj A B::A::F) :=
  (HeadRouting.front [A] F (.conj A B)).right f

def fresh {Γ Θ F U I J : List (NormalForm P)} {A B : NormalForm P}
    (k : G P (I++Γ) (J++A::F)) (g : G P Θ (B::U)) :
    G P ((I++Γ)++Θ) (.conj A B::((J++F)++U)) :=
  G.conjR ((HeadRouting.front J F A).right k) g

def adapted {Γ Θ F U I J : List (NormalForm P)} {A B : NormalForm P}
    (k : G P (I++Γ) (J++A::F)) (g : G P Θ (B::U)) :
    G P (I++(Γ++Θ)) (.conj A B::(J++(F++U))) :=
  ((ExchangeScript.appendAssoc J F U).consFixed (.conj A B)).structural.right
    ((ExchangeScript.appendAssoc I Γ Θ).structural.left (fresh k g))

theorem first_equation {Γ Θ F U I J : List (NormalForm P)} {A B : NormalForm P}
    (f : G P Γ (A::.conj A B::F)) (g : G P Θ (B::U)) (h : G P (.conj A B::I) J) :
    ofTerm ((HeadRouting.front J (F++U) (.conj A B)).right (G.cut (body f g) h)).denote =
      ofTerm (adapted (G.cut (child f) h) g).denote := by
  have he := BinaryLogical.conjLeftFirstNative_equation f g h
  rw [ExchangeScript.right_denote,body,he,BinaryLogical.conjLeftFirstNative,ExchangeScript.right_denote]
  have hc := (HeadRouting.front J (F++U) (.conj A B)).arrow_inverse .disj
  change comp ((HeadRouting.front J (F++U) (.conj A B)).inverse.arrow .disj)
    ((HeadRouting.front J (F++U) (.conj A B)).arrow .disj) = id _ at hc
  rw [Laws.assoc]
  erw [hc]
  erw [Laws.comp_id]
  simp only [adapted,fresh,ExchangeScript.structural_left,ExchangeScript.structural_right]
  rfl

def rebuild {Γ Θ F U I J : List (NormalForm P)} (C : NormalForm P)
    (l : G P (I++((I++Γ)++Θ)) (J++((J++F)++U))) : G P (I++(Γ++Θ)) (J++(F++U)) :=
  SequentialRepair.prefixRepair
    (SequentialAdapters.rightResult (ExchangeScript.appendAssoc I Γ Θ).structural
      ((ExchangeScript.appendAssoc J F U).consFixed C).structural
      (.here C (J++(F++U))) (.here C ((J++F)++U))
      (ExchangeScript.structural_singleFiber _ _ _ (ExchangeScript.consFixed_here C _)) l)

theorem native_equation {Γ Θ F U I J : List (NormalForm P)} {A B : NormalForm P}
    (f : G P Γ (A::.conj A B::F)) (g : G P Θ (B::U)) (h : G P (.conj A B::I) J) :
    ofTerm (G.cut (parent f g) h).denote =
      ofTerm (rebuild (.conj A B) (G.cut (fresh (G.cut (child f) h) g) h)).denote := by
  apply (SequentialRepair.headParentRight_equation (body f g) h).trans
  have he : ofTerm (SequentialRepair.rightTwoCuts (body f g) h).denote =
      ofTerm (G.cut (adapted (G.cut (child f) h) g) h).denote :=
    Rules.cut_congr (first_equation f g h) (g:=h.denote) rfl
  apply (SequentialRepair.prefixRepair_congr _ _ he).trans
  apply SequentialRepair.prefixRepair_congr
  have he := SequentialAdapters.right_equation (ExchangeScript.appendAssoc I Γ Θ).structural
    ((ExchangeScript.appendAssoc J F U).consFixed (.conj A B)).structural _ _
    (ExchangeScript.structural_singleFiber _ _ _ (ExchangeScript.consFixed_here (.conj A B) _))
    (fresh (G.cut (child f) h) g) h (.here (.conj A B) I)
  simp only [PositionalCut.head] at he
  exact he

end DosenPetric.Reduced.Gentzen.SequentialConjFirst
