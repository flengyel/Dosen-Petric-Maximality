module

public import DosenPetric.GentzenLastBlockSplit

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace BinaryLogical

def conjFirstNative {Γ Θ Δ Λ I D : List (NormalForm P)} {A B : NormalForm P}
    (k : G P (Γ ++ I) (A :: (Δ ++ D))) (g : G P Θ (B :: Λ)) :
    G P ((Γ ++ Θ) ++ I) ((.conj A B :: (Δ ++ Λ)) ++ D) :=
  (lastExchange (.conj A B :: Δ) D Λ).right
    ((lastExchange Γ I Θ).left (G.conjR k g))

def firstInput (Γ Θ I : List (NormalForm P)) :
    Hom (ante ((Γ ++ Θ) ++ I)) (.conj (.conj (ante Γ) (ante I)) (ante Θ)) :=
  comp (ofTerm (append .conj (Γ ++ Θ) I).invTerm)
    (comp (tensor .conj (ofTerm (append .conj Γ Θ).invTerm) (id (ante I)))
      (exchangeCore .conj (ante Γ) (ante Θ) (ante I)))

def firstOutput (Q : NormalForm P) (Δ Λ D : List (NormalForm P)) :
    Hom (.disj Q (.disj (.disj (succ Δ) (succ D)) (succ Λ)))
      (succ ((Q :: (Δ ++ Λ)) ++ D)) :=
  comp (tensor .disj (id Q) (tensor .disj (ofTerm (append .disj Δ D).toTerm) (id (succ Λ))))
    (comp (tensor .disj (id Q) (ofTerm (append .disj (Δ ++ D) Λ).toTerm))
      ((lastExchange (Q :: Δ) D Λ).arrow .disj))

theorem first_input (Γ Θ I : List (NormalForm P)) :
    comp ((lastExchange Γ I Θ).arrow .conj)
      (comp (ofTerm (append .conj (Γ ++ I) Θ).invTerm)
        (tensor .conj (ofTerm (append .conj Γ I).invTerm) (id (ante Θ)))) =
      firstInput Γ Θ I := by
  have he := lastExchange_split .conj Γ I Θ
  dsimp only [side,sideM,conjMonoidal,category,split] at he
  simpa only [firstInput,exchangeCore,Laws.assoc] using he

theorem first_output (Q : NormalForm P) (Δ Λ D : List (NormalForm P)) :
    comp (residualOutput Q (succ Δ) (succ D) (succ Λ))
      (comp (tensor .disj (tensor .disj (id Q) (ofTerm (append .disj Δ Λ).toTerm)) (id (succ D)))
        (ofTerm (append .disj (Q :: (Δ ++ Λ)) D).toTerm)) =
      firstOutput Q Δ Λ D := by
  have hc : (lastExchange (Q :: Δ) D Λ).arrow .disj =
      tensor .disj (id Q) ((lastExchange Δ D Λ).arrow .disj) :=
    ExchangeScript.consFixed_arrow (lastExchange Δ D Λ) Q .disj
  have he := lastExchange_split .disj Δ D Λ
  dsimp only [side,sideM,disjMonoidal,opposite,category,split] at he
  have ht : comp (tensor .disj (ofTerm (append .disj Δ D).toTerm) (id (succ Λ)))
      (comp (ofTerm (append .disj (Δ ++ D) Λ).toTerm) ((lastExchange Δ D Λ).arrow .disj)) =
      comp (exchangeCore .disj (succ Δ) (succ D) (succ Λ))
        (comp (tensor .disj (ofTerm (append .disj Δ Λ).toTerm) (id (succ D)))
          (ofTerm (append .disj (Δ ++ Λ) D).toTerm)) := by
    simpa only [exchangeCore,Laws.assoc] using he
  unfold firstOutput
  rw [hc,Laws.tensor_comp,Laws.id_comp,Laws.tensor_comp,Laws.id_comp,ht]
  have hd := split_cons .disj Q (Δ ++ Λ) D
  dsimp only [side,sideM,disjMonoidal,opposite,category,split] at hd
  rw [residualOutput,hd]
  simp only [Laws.assoc]
  have hn := Laws.assocR_nat .disj (id Q) (ofTerm (append .disj Δ Λ).toTerm) (id (succ D))
  rw [← Laws.assoc (assocR .disj Q (.disj (succ Δ) (succ Λ)) (succ D)),hn]
  simp only [Laws.assoc]
  rw [← Laws.assoc (assocR .disj Q (succ (Δ ++ Λ)) (succ D)),Laws.assocR_L,Laws.id_comp]
  simp only [Laws.tensor_comp,Laws.id_comp]

end BinaryLogical
end DosenPetric.Reduced.Gentzen
