module

public import DosenPetric.GentzenSequentialCutAdapters

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace SequentialLogical

theorem principal_factor_cast (o : Op) {F V : List (NormalForm P)} {C : NormalForm P}
    (a : At F C) (Q : NormalForm P) (he : a.erase = V) :
    ((principal a Q).reindex (congrArg (fun xs => C::Q::xs) he) rfl).arrow o =
      (side P o).comp ((HeadRouting.front [Q] V C).arrow o)
        ((side P o).comp (((a.toHead.reindex (congrArg (List.cons C) he) rfl).consFixed Q).arrow o)
          ((BinaryMix.swapWhole F [Q]).arrow o)) := by
  cases he
  exact principal_factor o a Q

end SequentialLogical
namespace BlockedSource

theorem headL_script {F D : List (NormalForm P)} (A : NormalForm P) (f : G P (F++[A]) D) :
    headL A f = (BinaryMix.swapWhole F [A]).left f := by rfl

theorem tailL_script {F D : List (NormalForm P)} (A : NormalForm P) (f : G P (A::F) D) :
    tailL A f = (BinaryMix.swapWhole F [A]).inverse.left f := by rfl

theorem head_disjLLast {F U D E : List (NormalForm P)} {A B : NormalForm P}
    (f : G P (F++[A]) D) (g : G P (U++[B]) E) :
    ofTerm ((BinaryMix.swapWhole (F++U) [.disj A B]).left (disjLLast f g)).denote =
      ofTerm (G.disjL (headL A f) (headL B g)).denote := by
  rw [disjLLast_eq,tailL_script,ExchangeScript.left_denote,ExchangeScript.left_denote,
    ← Laws.assoc]
  have he := (BinaryMix.swapWhole (F++U) [.disj A B]).arrow_inverse .conj
  change comp _ _ = id _ at he
  rw [he,Laws.id_comp]

end BlockedSource
namespace SequentialRepair

theorem headParent_reindex {F V D : List (NormalForm P)} {C : NormalForm P}
    (he : F = V) (g : G P (C::C::V) D) :
    headParent (g.reindex (congrArg (fun xs => C::C::xs) he.symm) rfl) =
      (headParent g).reindex (congrArg (List.cons C) he.symm) rfl := by
  cases he
  rfl

end SequentialRepair
namespace Route

theorem head_program_left_cast {K F V D : List (NormalForm P)} (C : NormalForm P)
    (p : Route K F) (he : F = V) (g : G P (C::V) D) :
    (p.head C).program.left (g.reindex (congrArg (List.cons C) he.symm) rfl) =
      ((p.cast rfl he).head C).program.left g := by
  cases he
  rfl

end Route
end DosenPetric.Reduced.Gentzen
