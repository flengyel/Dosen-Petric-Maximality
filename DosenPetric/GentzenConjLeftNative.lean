module

public import DosenPetric.GentzenConjLeftCore

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace BinaryLogical

theorem disj_cross_nat {U V : NormalForm P} (k : Hom U V) (C A : NormalForm P) :
    comp (tensor .disj (id A) (tensor .disj (id C) k)) ((sideM P .disj).cross C A V) =
      comp ((sideM P .disj).cross C A U) (tensor .disj (id C) (tensor .disj (id A) k)) := by
  have he := (sideM P .disj).cross_nat (id C) (id A) k
  dsimp only [sideM,side,disjMonoidal,opposite,category] at he ⊢
  exact he

theorem front_inverse_split (Q : NormalForm P) (J K : List (NormalForm P)) :
    comp (tensor .disj (id Q) (ofTerm (append .disj J K).toTerm))
      ((HeadRouting.front J K Q).inverse.arrow .disj) =
      comp ((sideM P .disj).cross (succ J) Q (succ K))
        (ofTerm (append .disj J (Q :: K)).toTerm) := by
  have hf := HeadRouting.front_split .disj J K Q
  have hp := (HeadRouting.front J K Q).inverse_arrow .disj
  dsimp only [side,sideM,disjMonoidal,opposite,category,split] at hf hp
  have he := congrArg (fun k => comp ((sideM P .disj).cross (succ J) Q (succ K))
    (comp k ((HeadRouting.front J K Q).inverse.arrow .disj))) hf
  simp only [Laws.assoc] at he
  rw [hp,Laws.comp_id] at he
  erw [← Laws.assoc ((sideM P .disj).cross (succ J) Q (succ K)),disj_cross_inverse,Laws.id_comp] at he
  exact he.symm

def conjLeftFirstNative {Γ Θ D Λ T J : List (NormalForm P)} {A B : NormalForm P}
    (k : G P (T ++ Γ) (J ++ (A :: D))) (g : G P Θ (B :: Λ)) :
    G P (T ++ (Γ ++ Θ)) (J ++ (.conj A B :: (D ++ Λ))) :=
  (HeadRouting.front J (D ++ Λ) (.conj A B)).inverse.right
    (((ExchangeScript.appendAssoc J D Λ).consFixed (.conj A B)).right
      ((ExchangeScript.appendAssoc T Γ Θ).left
        (G.conjR ((HeadRouting.front J D A).right k) g)))

def leftFirstInput (T Γ Θ : List (NormalForm P)) :
    Hom (ante (T ++ (Γ ++ Θ))) (.conj (.conj (ante T) (ante Γ)) (ante Θ)) :=
  comp (ofTerm (append .conj T (Γ ++ Θ)).invTerm)
    (comp (tensor .conj (id (ante T)) (ofTerm (append .conj Γ Θ).invTerm))
      (assocR .conj (ante T) (ante Γ) (ante Θ)))

def leftFirstOutput (Q : NormalForm P) (J D Λ : List (NormalForm P)) :
    Hom (.disj (succ J) (.disj Q (.disj (succ D) (succ Λ)))) (succ (J ++ (Q :: (D ++ Λ)))) :=
  comp (tensor .disj (id (succ J)) (tensor .disj (id Q) (ofTerm (append .disj D Λ).toTerm)))
    (ofTerm (append .disj J (Q :: (D ++ Λ))).toTerm)

theorem left_first_input (T Γ Θ : List (NormalForm P)) :
    comp ((ExchangeScript.appendAssoc T Γ Θ).arrow .conj)
      (comp (ofTerm (append .conj (T ++ Γ) Θ).invTerm)
        (tensor .conj (ofTerm (append .conj T Γ).invTerm) (id (ante Θ)))) =
      leftFirstInput T Γ Θ := by
  have he := split_assoc .conj T Γ Θ
  dsimp only [side,sideM,conjMonoidal,category,split] at he
  exact he

theorem left_first_output (Q : NormalForm P) (J D Λ : List (NormalForm P)) :
    comp (tensor .disj (id Q) (tensor .disj (ofTerm (append .disj J D).toTerm) (id (succ Λ))))
      (comp (tensor .disj (id Q) (ofTerm (append .disj (J ++ D) Λ).toTerm))
        (comp (((ExchangeScript.appendAssoc J D Λ).consFixed Q).arrow .disj)
          ((HeadRouting.front J (D ++ Λ) Q).inverse.arrow .disj))) =
      comp (tensor .disj (id Q) (assocL .disj (succ J) (succ D) (succ Λ)))
        (comp ((sideM P .disj).cross (succ J) Q (.disj (succ D) (succ Λ)))
          (leftFirstOutput Q J D Λ)) := by
  rw [ExchangeScript.consFixed_arrow]
  dsimp only [sideM,side,disjMonoidal,opposite,category]
  have hs := split_assoc .disj J D Λ
  dsimp only [side,sideM,disjMonoidal,opposite,category,split] at hs
  have ht : comp (tensor .disj (ofTerm (append .disj J D).toTerm) (id (succ Λ)))
      (comp (ofTerm (append .disj (J ++ D) Λ).toTerm) ((ExchangeScript.appendAssoc J D Λ).arrow .disj)) =
      comp (assocL .disj (succ J) (succ D) (succ Λ))
        (comp (tensor .disj (id (succ J)) (ofTerm (append .disj D Λ).toTerm))
          (ofTerm (append .disj J (D ++ Λ)).toTerm)) := by
    simpa only [Laws.assoc] using hs
  rw [← Laws.assoc (tensor .disj (id Q) (ofTerm (append .disj (J ++ D) Λ).toTerm)),
    Laws.tensor_comp,Laws.id_comp]
  rw [← Laws.assoc (tensor .disj (id Q) (tensor .disj (ofTerm (append .disj J D).toTerm) (id (succ Λ)))),
    Laws.tensor_comp,Laws.id_comp,ht]
  rw [tensor_factor .disj (id Q),tensor_factor .disj (id Q)]
  simp only [Laws.assoc]
  rw [front_inverse_split]
  erw [← Laws.assoc (tensor .disj (id Q) (tensor .disj (id (succ J)) (ofTerm (append .disj D Λ).toTerm))),
    disj_cross_nat]
  simp only [leftFirstOutput,Laws.assoc]
  rfl

end BinaryLogical
end DosenPetric.Reduced.Gentzen
