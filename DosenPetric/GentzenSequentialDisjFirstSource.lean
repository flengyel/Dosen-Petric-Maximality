module

public import DosenPetric.GentzenSequentialDisjFirstNative

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.SequentialDisjFirst
universe u
variable {P : Type u}

def firstChild {F D : List (NormalForm P)} {A C : NormalForm P}
    (a : At F C) (f : G P (F++[A]) D) : G P (A::C::a.erase) D :=
  (a.toHead.consFixed A).left (BlockedSource.headL A f)

def secondChild {U E : List (NormalForm P)} {B : NormalForm P}
    (g : G P (U++[B]) E) : G P (B::U) E := BlockedSource.headL B g

theorem selected_child {F D : List (NormalForm P)} {A B : NormalForm P}
    (a : At F (.disj A B)) (f : G P (F++[A]) D) :
    ofTerm ((SequentialLogical.principal a A).structural.left f).denote =
      ofTerm (child (firstChild a f)).denote := by
  rw [ExchangeScript.structural_left,ExchangeScript.left_denote,child,firstChild,
    ExchangeScript.left_denote,ExchangeScript.left_denote,BlockedSource.headL_script,
    ExchangeScript.left_denote,SequentialLogical.principal_factor]
  dsimp only [side,category]
  simp only [Laws.assoc]

theorem selected_body {F U D E : List (NormalForm P)} {A B : NormalForm P}
    (a : At F (.disj A B)) (f : G P (F++[A]) D) (g : G P (U++[B]) E) :
    ofTerm (((SequentialLogical.principal (a.before U) (.disj A B)).reindex
      (congrArg (fun xs => .disj A B::.disj A B::xs) (a.erase_before U)) rfl).left
        (BlockedSource.disjLLast f g)).denote =
      ofTerm (body (firstChild a f) (secondChild g)).denote := by
  have he := SequentialLogical.principal_factor_cast .conj (a.before U) (.disj A B) (a.erase_before U)
  change ((SequentialLogical.principal (a.before U) (.disj A B)).reindex
      (congrArg (fun xs => .disj A B::.disj A B::xs) (a.erase_before U)) rfl).arrow .conj =
    comp ((HeadRouting.front [.disj A B] (a.erase++U) (.disj A B)).arrow .conj)
    (comp (((LogicalDeletion.headBefore a U).consFixed (.disj A B)).arrow .conj)
      ((BinaryMix.swapWhole (F++U) [.disj A B]).arrow .conj)) at he
  rw [ExchangeScript.left_denote,he]
  simp only [Laws.assoc]
  have ht := BlockedSource.head_disjLLast f g
  rw [ExchangeScript.left_denote] at ht
  rw [ht]
  have hf := DisjLogical.headBefore_input_disjL (BlockedSource.headL A f) a (BlockedSource.headL B g)
  rw [ExchangeScript.left_denote] at hf
  rw [hf,body,ExchangeScript.left_denote]
  rfl

end DosenPetric.Reduced.Gentzen.SequentialDisjFirst
