module

public import DosenPetric.GentzenSequentialDisjSecondNative

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace LogicalDeletion

theorem headShift_cons_arrow (o : Op) (Q : NormalForm P) (F : List (NormalForm P))
    {U : List (NormalForm P)} {C : NormalForm P} (a : At U C) :
    (headShift (Q::F) a).arrow o =
      (side P o).comp ((HeadRouting.front [Q] (F++a.erase) C).arrow o)
        (((headShift F a).consFixed Q).arrow o) := by
  let S := side P o
  let M := sideM P o
  have hp : (a.toHead.structural.prefixFixed (Q::F)).arrow o =
      M.tensor (S.id Q) ((a.toHead.structural.prefixFixed F).arrow o) :=
    BinaryLogical.structural_consFixed_arrow (a.toHead.structural.prefixFixed F) Q o
  rw [BinaryMix.headShift_structural,ExchangeScript.consFixed_arrow,BinaryMix.headShift_structural,
    BinaryLogical.front_cons_arrow,ExchangeScript.seq_side_arrow,ExchangeScript.consFixed_arrow,hp]
  change S.comp (S.comp ((HeadRouting.front [Q] (F++a.erase) C).arrow o)
      (M.tensor (S.id Q) ((HeadRouting.front F a.erase C).arrow o)))
      (M.tensor (S.id Q) ((a.toHead.structural.prefixFixed F).arrow o)) =
    S.comp ((HeadRouting.front [Q] (F++a.erase) C).arrow o)
      (M.tensor (S.id Q) (S.comp ((HeadRouting.front F a.erase C).arrow o)
        ((a.toHead.structural.prefixFixed F).arrow o)))
  rw [S.assoc,M.tensor_comp,S.id_comp]

end LogicalDeletion
namespace SequentialLogical

theorem selected_component {F D : List (NormalForm P)} {Q C : NormalForm P}
    (a : At F C) (f : G P (F++[Q]) D) :
    ofTerm ((principal a Q).structural.left f).denote =
      ofTerm ((HeadRouting.front [Q] a.erase C).left
        ((a.toHead.consFixed Q).left (BlockedSource.headL Q f))).denote := by
  rw [ExchangeScript.structural_left,ExchangeScript.left_denote,ExchangeScript.left_denote,
    ExchangeScript.left_denote,BlockedSource.headL_script,ExchangeScript.left_denote,principal_factor]
  dsimp only [side,category]
  simp only [Laws.assoc]

end SequentialLogical
namespace SequentialDisjSecond

def firstChild {F D : List (NormalForm P)} {A : NormalForm P}
    (f : G P (F++[A]) D) : G P (A::F) D := BlockedSource.headL A f

def secondChild {U E : List (NormalForm P)} {B C : NormalForm P}
    (a : At U C) (g : G P (U++[B]) E) : G P (B::C::a.erase) E :=
  (a.toHead.consFixed B).left (BlockedSource.headL B g)

theorem selected_child {U E : List (NormalForm P)} {A B : NormalForm P}
    (a : At U (.disj A B)) (g : G P (U++[B]) E) :
    ofTerm ((SequentialLogical.principal a B).structural.left g).denote =
      ofTerm (child (secondChild a g)).denote :=
  SequentialLogical.selected_component a g

theorem selected_body {F U D E : List (NormalForm P)} {A B : NormalForm P}
    (a : At U (.disj A B)) (f : G P (F++[A]) D) (g : G P (U++[B]) E) :
    ofTerm (((SequentialLogical.principal (At.shift F a) (.disj A B)).reindex
      (congrArg (fun xs => .disj A B::.disj A B::xs) (At.erase_shift_at F a)) rfl).left
        (BlockedSource.disjLLast f g)).denote =
      ofTerm (body (firstChild f) (secondChild a g)).denote := by
  have he := SequentialLogical.principal_factor_cast .conj (At.shift F a) (.disj A B) (At.erase_shift_at F a)
  change ((SequentialLogical.principal (At.shift F a) (.disj A B)).reindex
      (congrArg (fun xs => .disj A B::.disj A B::xs) (At.erase_shift_at F a)) rfl).arrow .conj =
    comp ((HeadRouting.front [.disj A B] (F++a.erase) (.disj A B)).arrow .conj)
      (comp (((LogicalDeletion.headShift F a).consFixed (.disj A B)).arrow .conj)
        ((BinaryMix.swapWhole (F++U) [.disj A B]).arrow .conj)) at he
  rw [ExchangeScript.left_denote,he]
  simp only [Laws.assoc]
  have ht := BlockedSource.head_disjLLast f g
  rw [ExchangeScript.left_denote] at ht
  rw [ht]
  have ha := LogicalDeletion.headShift_cons_arrow .conj (.disj A B) F a
  change (LogicalDeletion.headShift (.disj A B::F) a).arrow .conj =
    comp ((HeadRouting.front [.disj A B] (F++a.erase) (.disj A B)).arrow .conj)
      (((LogicalDeletion.headShift F a).consFixed (.disj A B)).arrow .conj) at ha
  rw [← Laws.assoc,← ha]
  have hf := DisjLogical.headShift_input_disjL (BlockedSource.headL A f) (BlockedSource.headL B g) a
  rw [ExchangeScript.left_denote] at hf
  rw [hf]
  rfl

end SequentialDisjSecond
end DosenPetric.Reduced.Gentzen
