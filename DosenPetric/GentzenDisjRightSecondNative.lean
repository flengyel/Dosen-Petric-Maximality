module

public import DosenPetric.GentzenDisjRightCore

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace DisjLogical

def disjRightSecondNative {Γ Θ Δ Λ I D : List (NormalForm P)} {A B : NormalForm P}
    (f : G P (A :: Γ) Δ) (k : G P (B :: (Θ ++ I)) (Λ ++ D)) :
    G P ((.disj A B :: (Γ ++ Θ)) ++ I) ((Δ ++ Λ) ++ D) :=
  (ExchangeScript.appendAssoc Δ Λ D).inverse.right
    (((ExchangeScript.appendAssoc Γ Θ I).inverse.consFixed (.disj A B)).left (G.disjL f k))

theorem head_second_input (Q C : NormalForm P) (Γ Θ : List (NormalForm P)) :
    comp ((HeadRouting.front (Q :: Γ) Θ C).arrow .conj)
      (tensor .conj (id Q) (ofTerm (append .conj Γ (C :: Θ)).invTerm)) =
      comp (tensor .conj (id C) (tensor .conj (id Q) (ofTerm (append .conj Γ Θ).invTerm)))
        (secondDisjInput C (ante Γ) (ante Θ) Q) := by
  rw [BinaryLogical.front_cons_arrow]
  change comp (comp ((HeadRouting.front [Q] (Γ ++ Θ) C).arrow .conj)
    (((HeadRouting.front Γ Θ C).consFixed Q).arrow .conj)) _ = _
  rw [ExchangeScript.consFixed_arrow,HeadRouting.front_singleton]
  have hf := HeadRouting.front_split .conj Γ Θ C
  dsimp only [side,sideM,conjMonoidal,category,split] at hf ⊢
  rw [Laws.assoc,Laws.tensor_comp,Laws.id_comp,hf,tensor_factor .conj (id Q)]
  have hn := (sideM P .conj).cross_nat (id C) (id Q) (ofTerm (append .conj Γ Θ).invTerm)
  dsimp only [side,sideM,conjMonoidal,category] at hn
  rw [← Laws.assoc,hn]
  simp only [secondDisjInput,Laws.assoc]
  rfl

def rightSecondInput (Q : NormalForm P) (Γ Θ I : List (NormalForm P)) :
    Hom (ante ((Q :: (Γ ++ Θ)) ++ I)) (.conj Q (.conj (ante Γ) (.conj (ante Θ) (ante I)))) :=
  tensor .conj (id Q)
    (comp (ofTerm (append .conj (Γ ++ Θ) I).invTerm)
      (comp (tensor .conj (ofTerm (append .conj Γ Θ).invTerm) (id (ante I)))
        (assocL .conj (ante Γ) (ante Θ) (ante I))))

def rightSecondOutput (Δ Λ D : List (NormalForm P)) :
    Hom (.disj (succ Δ) (.disj (succ Λ) (succ D))) (succ ((Δ ++ Λ) ++ D)) :=
  comp (assocR .disj (succ Δ) (succ Λ) (succ D))
    (comp (tensor .disj (ofTerm (append .disj Δ Λ).toTerm) (id (succ D)))
      (ofTerm (append .disj (Δ ++ Λ) D).toTerm))

theorem right_second_input (Q : NormalForm P) (Γ Θ I : List (NormalForm P)) :
    comp (((ExchangeScript.appendAssoc Γ Θ I).inverse.consFixed Q).arrow .conj)
      (comp (tensor .conj (id Q) (ofTerm (append .conj Γ (Θ ++ I)).invTerm))
        (tensor .conj (id Q) (tensor .conj (id (ante Γ)) (ofTerm (append .conj Θ I).invTerm)))) =
      rightSecondInput Q Γ Θ I := by
  rw [ExchangeScript.consFixed_arrow]
  dsimp only [sideM,side,conjMonoidal,category]
  rw [Laws.tensor_comp,Laws.id_comp,Laws.tensor_comp,Laws.id_comp]
  have he := split_assoc_inverse .conj Γ Θ I
  dsimp only [side,sideM,conjMonoidal,category,split] at he
  rw [he]
  rfl

theorem right_second_parent_input (Q : NormalForm P) (Γ Θ I : List (NormalForm P)) :
    comp (ofTerm (append .conj (Q :: (Γ ++ Θ)) I).invTerm)
      (comp (tensor .conj (tensor .conj (id Q) (ofTerm (append .conj Γ Θ).invTerm)) (id (ante I)))
        (comp (assocL .conj Q (.conj (ante Γ) (ante Θ)) (ante I))
          (tensor .conj (id Q) (assocL .conj (ante Γ) (ante Θ) (ante I))))) =
      rightSecondInput Q Γ Θ I := by
  have hs := split_cons .conj Q (Γ ++ Θ) I
  dsimp only [side,sideM,conjMonoidal,category,split] at hs
  rw [hs]
  simp only [Laws.assoc]
  have hn := Laws.assocR_nat .conj (id Q) (ofTerm (append .conj Γ Θ).invTerm) (id (ante I))
  rw [← Laws.assoc (assocR .conj Q (ante (Γ ++ Θ)) (ante I)),hn]
  simp only [Laws.assoc]
  rw [← Laws.assoc (assocR .conj Q (.conj (ante Γ) (ante Θ)) (ante I)),Laws.assocR_L,Laws.id_comp]
  simp only [rightSecondInput,Laws.tensor_comp,Laws.id_comp]

theorem right_second_output (Δ Λ D : List (NormalForm P)) :
    comp (tensor .disj (id (succ Δ)) (ofTerm (append .disj Λ D).toTerm))
      (comp (ofTerm (append .disj Δ (Λ ++ D)).toTerm) ((ExchangeScript.appendAssoc Δ Λ D).inverse.arrow .disj)) =
      rightSecondOutput Δ Λ D := by
  have he := split_assoc_inverse .disj Δ Λ D
  dsimp only [side,sideM,disjMonoidal,opposite,category,split] at he
  simpa only [rightSecondOutput,Laws.assoc] using he

end DisjLogical
end DosenPetric.Reduced.Gentzen
