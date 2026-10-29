module

public import DosenPetric.GentzenDisjRightFirstCore

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace DisjLogical

def disjRightFirstNative {Γ Θ Δ Λ I D : List (NormalForm P)} {A B : NormalForm P}
    (k : G P (A :: (Γ ++ I)) (Δ ++ D)) (g : G P (B :: Θ) Λ) :
    G P ((.disj A B :: (Γ ++ Θ)) ++ I) ((Δ ++ Λ) ++ D) :=
  (BinaryLogical.lastExchange Δ D Λ).right
    ((BinaryLogical.lastExchange (.disj A B :: Γ) I Θ).left (G.disjL k g))

theorem head_first_input (Q C : NormalForm P) (Γ Θ : List (NormalForm P)) :
    comp ((HeadRouting.front [Q] (Γ ++ Θ) C).arrow .conj)
      (tensor .conj (id Q) (ofTerm (append .conj (C :: Γ) Θ).invTerm)) =
      comp (tensor .conj (id C) (tensor .conj (id Q) (ofTerm (append .conj Γ Θ).invTerm)))
        (firstDisjInput C (ante Γ) (ante Θ) Q) := by
  rw [HeadRouting.front_singleton]
  have hf := split_cons .conj C Γ Θ
  dsimp only [side,sideM,conjMonoidal,category,split] at hf ⊢
  rw [hf,tensor_factor .conj (id Q)]
  have hn := (sideM P .conj).cross_nat (id C) (id Q) (ofTerm (append .conj Γ Θ).invTerm)
  dsimp only [side,sideM,conjMonoidal,category] at hn
  rw [← Laws.assoc,hn]
  simp only [firstDisjInput,Laws.assoc]
  rfl

def rightFirstInput (Q : NormalForm P) (Γ Θ I : List (NormalForm P)) :
    Hom (ante ((Q :: (Γ ++ Θ)) ++ I)) (.conj Q (.conj (.conj (ante Γ) (ante I)) (ante Θ))) :=
  tensor .conj (id Q) (BinaryLogical.firstInput Γ Θ I)

def rightFirstOutput (Δ Λ D : List (NormalForm P)) :
    Hom (.disj (.disj (succ Δ) (succ D)) (succ Λ)) (succ ((Δ ++ Λ) ++ D)) :=
  comp (BinaryLogical.exchangeCore .disj (succ Δ) (succ D) (succ Λ))
    (comp (tensor .disj (ofTerm (append .disj Δ Λ).toTerm) (id (succ D)))
      (ofTerm (append .disj (Δ ++ Λ) D).toTerm))

theorem right_first_input (Q : NormalForm P) (Γ Θ I : List (NormalForm P)) :
    comp ((BinaryLogical.lastExchange (Q :: Γ) I Θ).arrow .conj)
      (comp (tensor .conj (id Q) (ofTerm (append .conj (Γ ++ I) Θ).invTerm))
        (tensor .conj (id Q) (tensor .conj (ofTerm (append .conj Γ I).invTerm) (id (ante Θ))))) =
      rightFirstInput Q Γ Θ I := by
  have hc : (BinaryLogical.lastExchange (Q :: Γ) I Θ).arrow .conj =
      tensor .conj (id Q) ((BinaryLogical.lastExchange Γ I Θ).arrow .conj) :=
    ExchangeScript.consFixed_arrow (BinaryLogical.lastExchange Γ I Θ) Q .conj
  rw [hc,Laws.tensor_comp,Laws.id_comp,Laws.tensor_comp,Laws.id_comp,BinaryLogical.first_input]
  rfl

theorem right_first_parent_input (Q : NormalForm P) (Γ Θ I : List (NormalForm P)) :
    comp (ofTerm (append .conj (Q :: (Γ ++ Θ)) I).invTerm)
      (comp (tensor .conj (tensor .conj (id Q) (ofTerm (append .conj Γ Θ).invTerm)) (id (ante I)))
        (comp (assocL .conj Q (.conj (ante Γ) (ante Θ)) (ante I))
          (tensor .conj (id Q) (BinaryLogical.exchangeCore .conj (ante Γ) (ante Θ) (ante I))))) =
      rightFirstInput Q Γ Θ I := by
  have hs := split_cons .conj Q (Γ ++ Θ) I
  dsimp only [side,sideM,conjMonoidal,category,split] at hs
  rw [hs]
  simp only [Laws.assoc]
  have hn := Laws.assocR_nat .conj (id Q) (ofTerm (append .conj Γ Θ).invTerm) (id (ante I))
  rw [← Laws.assoc (assocR .conj Q (ante (Γ ++ Θ)) (ante I)),hn]
  simp only [Laws.assoc]
  rw [← Laws.assoc (assocR .conj Q (.conj (ante Γ) (ante Θ)) (ante I)),Laws.assocR_L,Laws.id_comp]
  simp only [rightFirstInput,BinaryLogical.firstInput,Laws.tensor_comp,Laws.id_comp]

theorem right_first_output (Δ Λ D : List (NormalForm P)) :
    comp (tensor .disj (ofTerm (append .disj Δ D).toTerm) (id (succ Λ)))
      (comp (ofTerm (append .disj (Δ ++ D) Λ).toTerm) ((BinaryLogical.lastExchange Δ D Λ).arrow .disj)) =
      rightFirstOutput Δ Λ D := by
  have he := BinaryLogical.lastExchange_split .disj Δ D Λ
  dsimp only [side,sideM,disjMonoidal,opposite,category,split] at he
  simpa only [rightFirstOutput,BinaryLogical.exchangeCore,Laws.assoc] using he

end DisjLogical
end DosenPetric.Reduced.Gentzen
