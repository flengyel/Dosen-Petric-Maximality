module

public import DosenPetric.GentzenConjSecondNative

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace BinaryLogical

theorem front_cons_arrow (o : Op) (A C : NormalForm P) (F U : List (NormalForm P)) :
    (HeadRouting.front (A :: F) U C).arrow o =
      ((HeadRouting.front [A] (F ++ U) C).seq ((HeadRouting.front F U C).consFixed A)).arrow o := by
  apply side_ext o
  intro E b
  rw [ExchangeScript.component,ExchangeScript.component]
  change component o _ = component o ((HeadRouting.front [A] (F ++ U) C).get
    (((HeadRouting.front F U C).consFixed A).get b))
  apply congrArg (component o)
  apply At.index_injective
  rw [HeadRouting.front_index]
  cases b with
  | here =>
    erw [ExchangeScript.consFixed_here,HeadRouting.front_index]
    simp only [At.index,List.length_cons,List.length_nil,exchangeIndex,Nat.not_lt_zero,Nat.zero_add,ite_false]
    repeat first | split | omega
  | there b =>
    rw [ExchangeScript.consFixed_there,HeadRouting.front_index]
    simp only [At.index]
    rw [HeadRouting.front_index]
    simp only [List.length_cons,List.length_nil,exchangeIndex,Nat.not_lt_zero,Nat.zero_add,ite_false]
    repeat first | split | omega

theorem leftSecondParent_selected {Γ Θ D E : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P Γ (A :: D)) (g : G P Θ (B :: C :: E)) :
    ofTerm ((HeadRouting.front (.conj A B :: D) E C).right
      (G.conjR (Δ := D) (Λ := C :: E) f g)).denote =
      comp (ofTerm (append .conj Γ Θ).invTerm)
        (comp (tensor .conj (ofTerm f.denote) (ofTerm g.denote))
          (comp (selectedMixedSecond A (succ D) B C (succ E))
            (tensor .disj (id C) (tensor .disj (id (.conj A B)) (ofTerm (append .disj D E).toTerm))))) := by
  rw [ExchangeScript.right_denote,G.denote_conjR,front_cons_arrow]
  simp only [Rules.conjRight,ofTerm_comp,ofTerm_tensor,ofTerm_id]
  change comp (comp _ (comp _ (comp _ _)))
    (comp (((HeadRouting.front D E C).consFixed (.conj A B)).arrow .disj)
      ((HeadRouting.front [.conj A B] (D ++ E) C).arrow .disj)) = _
  rw [ExchangeScript.consFixed_arrow,HeadRouting.front_singleton]
  have hs := HeadRouting.front_split .disj D E C
  dsimp only [sideM,side,disjMonoidal,opposite,category,split] at hs ⊢
  simp only [Laws.assoc]
  rw [← Laws.assoc (tensor .disj (id (.conj A B)) (ofTerm (append .disj D (C :: E)).toTerm)),
    Laws.tensor_comp,Laws.id_comp,hs,tensor_factor .disj (id (.conj A B))]
  simp only [Laws.assoc]
  erw [disj_cross_nat]
  simp only [selectedMixedSecond,Laws.assoc]
  all_goals rfl

theorem leftSecondParent_denote {Γ Θ D E T J : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P Γ (A :: D)) (g : G P Θ (B :: C :: E)) (h : G P (C :: T) J) :
    ofTerm (G.cut ((HeadRouting.front (.conj A B :: D) E C).right
      (G.conjR (Δ := D) (Λ := C :: E) f g)) h).denote =
      comp (leftSecondInput T Γ Θ)
        (comp (tensor .conj (ofTerm f.denote)
          (comp (splice (comp (ofTerm g.denote) ((sideM P .disj).cross C B (succ E))) (ofTerm h.denote))
            ((sideM P .disj).cross B (succ J) (succ E))))
          (comp (selectedMixedSecond A (succ D) B (succ J) (succ E))
            (leftFirstOutput (.conj A B) J D E))) := by
  have hs : splice (comp (tensor .conj (ofTerm f.denote) (ofTerm g.denote))
      (comp (selectedMixedSecond A (succ D) B C (succ E))
        (tensor .disj (id C) (tensor .disj (id (.conj A B)) (ofTerm (append .disj D E).toTerm)))))
        (ofTerm h.denote) =
      comp (splice (comp (tensor .conj (ofTerm f.denote) (ofTerm g.denote))
        (selectedMixedSecond A (succ D) B C (succ E))) (ofTerm h.denote))
          (tensor .disj (id (succ J)) (tensor .disj (id (.conj A B)) (ofTerm (append .disj D E).toTerm))) := by
    simpa only [Laws.assoc] using Splice.residual
      (tensor .disj (id (.conj A B)) (ofTerm (append .disj D E).toTerm))
      (comp (tensor .conj (ofTerm f.denote) (ofTerm g.denote)) (selectedMixedSecond A (succ D) B C (succ E)))
      (ofTerm h.denote)
  rw [cut_splice,leftSecondParent_selected,Splice.input]
  erw [hs,conjR_left_second_core]
  simp only [leftSecondInput,leftFirstOutput,Laws.assoc]
  all_goals rfl

end BinaryLogical
end DosenPetric.Reduced.Gentzen
