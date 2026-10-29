module

public import DosenPetric.GentzenSequentialRightCutDenotation

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

theorem logicalSide_prefix (o : Op) (F U : List (NormalForm P)) (A B : NormalForm P) :
    prefixSide o F (logicalSide o [] U A B) = logicalSide o F U A B := by
  induction F with
  | nil => rfl
  | cons H F ih => rw [prefixSide,logicalSide_cons,ih]; rfl

namespace SequentialDisjunction

def body {F D : List (NormalForm P)} {A B : NormalForm P}
    (f : G P F (.disj A B::A::B::D)) : G P F (.disj A B::.disj A B::D) :=
  G.disjR F [.disj A B] D A B f

def parent {F D : List (NormalForm P)} {A B : NormalForm P}
    (f : G P F (.disj A B::A::B::D)) : G P F (.disj A B::D) :=
  SequentialRepair.headParentRight (body f)

/-- Only equality transport follows the native rule; component exchanges are below it. -/
def fresh {F D J : List (NormalForm P)} {A B : NormalForm P}
    (k : G P F (J++A::B::D)) : G P F (.disj A B::(J++D)) :=
  (G.disjR F [] (At.shift J (.here (.disj A B) D)).erase A B
    ((LogicalHeadRouting.components J D A B (.disj A B)).right k)).reindex rfl
      (congrArg (List.cons (.disj A B)) (At.erase_shift J D (.disj A B)))

theorem front_native {F D J : List (NormalForm P)} {A B : NormalForm P}
    (k : G P F (J++A::B::D)) :
    ofTerm ((HeadRouting.front J D (.disj A B)).right (G.disjR F J D A B k)).denote =
      ofTerm (fresh k).denote := by
  have he := G.reindex_congr rfl (congrArg (List.cons (.disj A B)) (At.erase_shift J D (.disj A B)))
    (G.disjR_toHead F J D A B k)
  exact he

theorem first_equation {F D I J : List (NormalForm P)} {A B : NormalForm P}
    (f : G P F (.disj A B::A::B::D)) (h : G P (.disj A B::I) J) :
    ofTerm ((HeadRouting.front J D (.disj A B)).right (G.cut (body f) h)).denote =
      ofTerm (fresh (G.cut f h)).denote := by
  have he := CutCommutation.same_disjR_before f (.here (.disj A B) []) h (.here (.disj A B) I)
  change ofTerm (G.cut (body f) h).denote =
    ofTerm (PrefixedLogical.disjR (I++F) J [] D A B (G.cut f h)).denote at he
  have hp : ofTerm (PrefixedLogical.disjR (I++F) J [] D A B (G.cut f h)).denote =
      ofTerm (G.disjR (I++F) J D A B (G.cut f h)).denote := by
    rw [PrefixedLogical.disjR_denote,G.denote_disjR,disjRight_compare]
    change comp _ (prefixSide .disj J (logicalSide .disj [] D A B)) =
      comp _ (logicalSide .disj J D A B)
    rw [logicalSide_prefix]
  apply (Eq.trans ?_ (front_native (G.cut f h)))
  rw [ExchangeScript.right_denote,ExchangeScript.right_denote,he,hp]

theorem native_equation {F D I J : List (NormalForm P)} {A B : NormalForm P}
    (f : G P F (.disj A B::A::B::D)) (h : G P (.disj A B::I) J) :
    ofTerm (G.cut (parent f) h).denote =
      ofTerm (SequentialRepair.prefixRepair (G.cut (fresh (G.cut f h)) h)).denote := by
  apply (SequentialRepair.headParentRight_equation (body f) h).trans
  apply SequentialRepair.prefixRepair_congr
  exact Rules.cut_congr (first_equation f h) rfl

end SequentialDisjunction
end DosenPetric.Reduced.Gentzen
