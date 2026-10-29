module

public import DosenPetric.GentzenSequentialConjFirstNative

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace LogicalDeletion

theorem headUnder_singleton_arrow (o : Op) {F : List (NormalForm P)} {C : NormalForm P}
    (a : At F C) (Q : NormalForm P) :
    (headUnder [] [Q] a).arrow o =
      ((HeadRouting.front [Q] a.erase C).seq (a.toHead.consFixed Q)).arrow o := by
  change a.there.toHead.arrow o = _
  exact BinaryLogical.toHead_there_arrow o Q a

end LogicalDeletion
namespace SequentialConjFirst

def firstChild {Γ F : List (NormalForm P)} {A C : NormalForm P}
    (a : At F C) (f : G P Γ (A::F)) : G P Γ (A::C::a.erase) :=
  (a.toHead.consFixed A).right f

theorem selected_body {Γ Θ F U : List (NormalForm P)} {A B : NormalForm P}
    (a : At F (.conj A B)) (f : G P Γ (A::F)) (g : G P Θ (B::U)) :
    ofTerm (((LogicalDeletion.headUnder [] [.conj A B] (a.before U)).reindex
      (congrArg (fun xs => .conj A B::.conj A B::xs) (a.erase_before U)) rfl).right
        (G.conjR (Δ:=F) (Λ:=U) f g)).denote =
      ofTerm (body (firstChild a f) g).denote := by
  have he := BinaryLogical.leftFirstParent_factor f a g
  rw [ExchangeScript.right_denote] at he
  rw [ExchangeScript.right_denote]
  exact he

theorem rebuild_count {Γ Θ F U I J : List (NormalForm P)} (C : NormalForm P)
    (l : G P (I++((I++Γ)++Θ)) (J++((J++F)++U))) : (rebuild C l).cutCount = l.cutCount := by
  rw [rebuild,SequentialRepair.prefixRepair_count,SequentialAdapters.rightResult_count]

theorem rebuild_congr {Γ Θ F U I J : List (NormalForm P)} (C : NormalForm P)
    (l l' : G P (I++((I++Γ)++Θ)) (J++((J++F)++U)))
    (he : ofTerm l.denote = ofTerm l'.denote) : ofTerm (rebuild C l).denote = ofTerm (rebuild C l').denote :=
  SequentialRepair.prefixRepair_congr _ _ (SequentialAdapters.rightResult_congr _ _ _ _ _ _ _ he)

end SequentialConjFirst
end DosenPetric.Reduced.Gentzen
