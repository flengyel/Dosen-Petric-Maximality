module

public import DosenPetric.GentzenSequentialConjSecondNative

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.SequentialConjSecond
universe u
variable {P : Type u}

def secondChild {Θ U : List (NormalForm P)} {B C : NormalForm P}
    (a : At U C) (g : G P Θ (B::U)) : G P Θ (B::C::a.erase) :=
  (a.toHead.consFixed B).right g

theorem selected_body {Γ Θ F U : List (NormalForm P)} {A B : NormalForm P}
    (a : At U (.conj A B)) (f : G P Γ (A::F)) (g : G P Θ (B::U)) :
    ofTerm (((LogicalDeletion.headUnder [] [.conj A B] (At.shift F a)).reindex
      (congrArg (fun xs => .conj A B::.conj A B::xs) (At.erase_shift_at F a)) rfl).right
        (G.conjR (Δ:=F) (Λ:=U) f g)).denote =
      ofTerm (body f (secondChild a g)).denote := by
  have he := BinaryLogical.headShift_residual_conjR f g a
  rw [ExchangeScript.right_denote] at he
  rw [ExchangeScript.right_denote]
  exact he

theorem rebuild_count {Γ Θ F U I J : List (NormalForm P)} (C : NormalForm P)
    (l : G P (I++(Γ++(I++Θ))) (J++(F++(J++U)))) : (rebuild C l).cutCount = l.cutCount := by
  rw [rebuild,SequentialRepair.prefixRepair_count,SequentialAdapters.rightResult_count]

theorem rebuild_congr {Γ Θ F U I J : List (NormalForm P)} (C : NormalForm P)
    (l l' : G P (I++(Γ++(I++Θ))) (J++(F++(J++U))))
    (he : ofTerm l.denote = ofTerm l'.denote) : ofTerm (rebuild C l).denote = ofTerm (rebuild C l').denote :=
  SequentialRepair.prefixRepair_congr _ _ (SequentialAdapters.rightResult_congr _ _ _ _ _ _ _ he)

end DosenPetric.Reduced.Gentzen.SequentialConjSecond
