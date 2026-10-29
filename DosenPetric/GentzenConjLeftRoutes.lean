module

public import DosenPetric.GentzenConjLeftEquation

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace BinaryLogical

theorem toHead_there_arrow {Δ : List (NormalForm P)} {C : NormalForm P}
    (o : Op) (A : NormalForm P) (a : At Δ C) :
    (At.there (B := A) a).toHead.arrow o =
      ((HeadRouting.front [A] a.erase C).seq (a.toHead.consFixed A)).arrow o := by
  apply side_ext o
  intro E b
  rw [ExchangeScript.component,ExchangeScript.component]
  change component o _ = component o ((HeadRouting.front [A] a.erase C).get ((a.toHead.consFixed A).get b))
  apply congrArg (component o)
  apply At.index_injective
  rw [At.toHead_get_index]
  cases b with
  | here =>
    rw [ExchangeScript.consFixed_here,HeadRouting.front_index]
    simp only [At.index,List.length_singleton]
    unfold exchangeIndex
    split <;> (try split) <;> (try split) <;> omega
  | there b =>
    rw [ExchangeScript.consFixed_there,HeadRouting.front_index]
    simp only [At.index,List.length_singleton]
    rw [At.toHead_get_index]
    simp only [exchangeIndex,Nat.not_lt_zero,Nat.zero_add,ite_false]
    repeat first | split | omega

theorem headBefore_there_arrow {Δ : List (NormalForm P)} {C : NormalForm P}
    (o : Op) (Q : NormalForm P) (a : At Δ C) (Λ : List (NormalForm P)) :
    (((At.there (B := Q) (a.before Λ)).toHead).reindex
      (congrArg (fun xs => C :: (Q :: xs)) (a.erase_before Λ)) rfl).arrow o =
      ((HeadRouting.front [Q] (a.erase ++ Λ) C).seq
        ((LogicalDeletion.headBefore a Λ).consFixed Q)).arrow o := by
  apply side_ext o
  intro E b
  rw [ExchangeScript.component,ExchangeScript.component]
  apply congrArg (component o)
  apply At.index_injective
  change ((((At.there (B := Q) (a.before Λ)).toHead.get b)).cast _).index =
    ((HeadRouting.front [Q] (a.erase ++ Λ) C).get
      (((LogicalDeletion.headBefore a Λ).consFixed Q).get b)).index
  rw [At.index_cast,At.toHead_get_index]
  cases b with
  | here =>
    rw [ExchangeScript.consFixed_here,HeadRouting.front_index]
    simp only [At.index,List.length_singleton,At.index_before]
    unfold exchangeIndex
    split <;> (try split) <;> (try split) <;> omega
  | there b =>
    rw [ExchangeScript.consFixed_there,HeadRouting.front_index]
    simp only [At.index,List.length_singleton,At.index_before]
    rw [LogicalDeletion.headBefore_index]
    simp only [exchangeIndex,Nat.not_lt_zero,Nat.zero_add,ite_false]
    repeat first | split | omega

theorem structural_consFixed_arrow {F U : List (NormalForm P)}
    (p : StructuralProgram P F U) (A : NormalForm P) (o : Op) :
    (p.consFixed A).arrow o = (sideM P o).tensor ((side P o).id A) (p.arrow o) := by
  let C := side P o
  let D := sideD P o
  apply side_ext o
  intro E a
  rw [StructuralProgram.component]
  cases a with
  | here => rw [StructuralProgram.consFixed_here,component_here,component_here,← D.fst_nat,C.comp_id]
  | there a =>
    rw [StructuralProgram.consFixed_there,component_there,component_there,← C.assoc,
      ← D.snd_nat,C.assoc,StructuralProgram.component]

theorem residual_first_conjR {F U Γ Θ Λ : List (NormalForm P)} {A B : NormalForm P}
    (p : StructuralProgram P F U) (f : G P Γ (A :: U)) (g : G P Θ (B :: Λ)) :
    ofTerm (((p.suffixFixed Λ).consFixed (.conj A B)).right (G.conjR f g)).denote =
      ofTerm (G.conjR ((p.consFixed A).right f) g).denote := by
  rw [StructuralProgram.right_denote,G.denote_conjR,G.denote_conjR]
  simp only [Rules.conjRight,ofTerm_comp,ofTerm_tensor,ofTerm_id]
  rw [StructuralProgram.right_denote]
  have hq := structural_consFixed_arrow (p.suffixFixed Λ) (.conj A B) .disj
  have hp := structural_consFixed_arrow p A .disj
  rw [hq,hp]
  have hs := p.suffixFixed_split .disj Λ
  dsimp only [side,sideM,disjMonoidal,opposite,category,split] at hs ⊢
  simp only [Laws.assoc]
  rw [Laws.tensor_comp,Laws.id_comp,hs]
  rw [tensor_factor .disj (id (.conj A B))]
  have hm := mixedDisj_nat (id A) (p.arrow .disj) (id B) (id (succ Λ))
  rw [Laws.tensor_id,Laws.tensor_id] at hm
  erw [← Laws.assoc (ofTerm (Term.mixedDisj A (succ U) B (succ Λ))),hm]
  simp only [Laws.assoc]
  rw [← Laws.assoc (tensor .conj (ofTerm f.denote) (ofTerm g.denote)),Laws.tensor_comp,Laws.comp_id]

end BinaryLogical
end DosenPetric.Reduced.Gentzen
