module

public import DosenPetric.GentzenDisjRuleLaws

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace DisjLogical

def disjFirstNative {Γ Θ D Λ T J : List (NormalForm P)} {A B : NormalForm P}
    (k : G P (T ++ (A :: Γ)) (J ++ D)) (g : G P (B :: Θ) Λ) :
    G P (T ++ (.disj A B :: (Γ ++ Θ))) (J ++ (D ++ Λ)) :=
  (ExchangeScript.appendAssoc J D Λ).right
    ((HeadRouting.front T (Γ ++ Θ) (.disj A B)).inverse.left
      (((ExchangeScript.appendAssoc T Γ Θ).consFixed (.disj A B)).left
        (G.disjL ((HeadRouting.front T Γ A).left k) g)))

theorem conj_front_inverse_split (Q : NormalForm P) (F U : List (NormalForm P)) :
    comp ((HeadRouting.front F U Q).inverse.arrow .conj)
      (tensor .conj (id Q) (ofTerm (append .conj F U).invTerm)) =
      comp (ofTerm (append .conj F (Q :: U)).invTerm)
        ((sideM P .conj).cross (ante F) Q (ante U)) := by
  have hf := HeadRouting.front_split .conj F U Q
  have hp := (HeadRouting.front F U Q).inverse_arrow .conj
  dsimp only [side,sideM,conjMonoidal,category,split] at hf hp
  have hi : comp ((sideM P .conj).cross Q (ante F) (ante U))
      ((sideM P .conj).cross (ante F) Q (ante U)) = id (.conj Q (.conj (ante F) (ante U))) :=
    (conjDiagonal P).cross_inverse (rightOut_assocR .conj) (side_swap_snd .conj) Q (ante F) (ante U)
  have he := congrArg (fun k => comp ((HeadRouting.front F U Q).inverse.arrow .conj)
    (comp k ((sideM P .conj).cross (ante F) Q (ante U)))) hf
  simp only [Laws.assoc] at he
  rw [← Laws.assoc ((HeadRouting.front F U Q).inverse.arrow .conj),hp,Laws.id_comp] at he
  erw [hi,Laws.comp_id] at he
  exact he.symm

def disjFirstInput (Q : NormalForm P) (T Γ Θ : List (NormalForm P)) :
    Hom (ante (T ++ (Q :: (Γ ++ Θ)))) (.conj Q (.conj (.conj (ante T) (ante Γ)) (ante Θ))) :=
  comp (ofTerm (append .conj T (Q :: (Γ ++ Θ))).invTerm)
    (comp (tensor .conj (id (ante T)) (tensor .conj (id Q) (ofTerm (append .conj Γ Θ).invTerm)))
      (firstDisjInput (ante T) (ante Γ) (ante Θ) Q))

def disjFirstOutput (J D Λ : List (NormalForm P)) :
    Hom (.disj (succ J) (.disj (succ D) (succ Λ))) (succ (J ++ (D ++ Λ))) :=
  comp (tensor .disj (id (succ J)) (ofTerm (append .disj D Λ).toTerm))
    (ofTerm (append .disj J (D ++ Λ)).toTerm)

theorem disj_first_input (Q : NormalForm P) (T Γ Θ : List (NormalForm P)) :
    comp ((HeadRouting.front T (Γ ++ Θ) Q).inverse.arrow .conj)
      (comp (((ExchangeScript.appendAssoc T Γ Θ).consFixed Q).arrow .conj)
        (comp (tensor .conj (id Q) (ofTerm (append .conj (T ++ Γ) Θ).invTerm))
          (tensor .conj (id Q) (tensor .conj (ofTerm (append .conj T Γ).invTerm) (id (ante Θ)))))) =
      disjFirstInput Q T Γ Θ := by
  have hs := split_assoc .conj T Γ Θ
  dsimp only [side,sideM,conjMonoidal,category,split] at hs
  rw [ExchangeScript.consFixed_arrow]
  dsimp only [side,sideM,conjMonoidal,category]
  rw [Laws.tensor_comp,Laws.id_comp,Laws.tensor_comp,Laws.id_comp,hs]
  rw [tensor_factor .conj (id Q),tensor_factor .conj (id Q)]
  rw [← Laws.assoc ((HeadRouting.front T (Γ ++ Θ) Q).inverse.arrow .conj),conj_front_inverse_split]
  have hn := (sideM P .conj).cross_nat (id (ante T)) (id Q) (ofTerm (append .conj Γ Θ).invTerm)
  dsimp only [side,sideM,conjMonoidal,category] at hn
  simp only [Laws.assoc]
  erw [← Laws.assoc ((sideM P .conj).cross (ante T) Q (ante (Γ ++ Θ))),hn]
  simp only [disjFirstInput,firstDisjInput,Laws.assoc]
  rfl

theorem disj_first_output (J D Λ : List (NormalForm P)) :
    comp (tensor .disj (ofTerm (append .disj J D).toTerm) (id (succ Λ)))
      (comp (ofTerm (append .disj (J ++ D) Λ).toTerm) ((ExchangeScript.appendAssoc J D Λ).arrow .disj)) =
      comp (assocL .disj (succ J) (succ D) (succ Λ)) (disjFirstOutput J D Λ) := by
  have he := split_assoc .disj J D Λ
  dsimp only [side,sideM,disjMonoidal,opposite,category,split] at he
  simpa only [disjFirstOutput,Laws.assoc] using he

end DisjLogical
end DosenPetric.Reduced.Gentzen
