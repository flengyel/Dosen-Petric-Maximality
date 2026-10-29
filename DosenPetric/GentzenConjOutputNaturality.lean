module

public import DosenPetric.GentzenBlockedRightConjEquation

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace Route

theorem head_compose {F K U : List (NormalForm P)} (p : Route K U) (q : Route U F) (A : NormalForm P) :
    (p.head A).compose (q.head A) = (p.compose q).head A := by
  apply ext_get
  intro B a
  cases a with
  | here => rw [compose_get,head_here,head_here,head_here]
  | there a => rw [compose_get,head_there,head_there,head_there,compose_get]

end Route
namespace Rules

theorem conjRight_output_nat {Γ Θ F U K L : List (NormalForm P)} {A B : NormalForm P}
    (p : Route K F) (q : Route L U)
    (f : Term P (ante Γ) (succ (A::F))) (g : Term P (ante Θ) (succ (B::U))) :
    comp (ofTerm (conjRight f g)) (((p.parallel q).head (.conj A B)).sideArrow .disj) =
      ofTerm (conjRight (.comp f (p.head A).coproduct) (.comp g (q.head B).coproduct)) := by
  have hs := Route.parallel_split .disj p q
  have hp := Route.head_side .disj A p
  have hq := Route.head_side .disj B q
  rw [Route.head_side]
  dsimp only [side,sideM,disjMonoidal,opposite,category,split] at hs hp hq ⊢
  change ofTerm (p.head A).coproduct = tensor .disj (id A) (p.sideArrow .disj) at hp
  change ofTerm (q.head B).coproduct = tensor .disj (id B) (q.sideArrow .disj) at hq
  simp only [conjRight,ofTerm_comp,ofTerm_tensor,ofTerm_id,Laws.assoc]
  erw [Laws.tensor_comp,Laws.id_comp,hs]
  rw [tensor_factor .disj (id (.conj A B))]
  have hm := mixedDisj_nat (id A) (p.sideArrow .disj) (id B) (q.sideArrow .disj)
  rw [Laws.tensor_id] at hm
  erw [← Laws.assoc (ofTerm (Term.mixedDisj A (succ F) B (succ U))),hm]
  erw [hp,hq]
  simp only [Laws.assoc]
  rw [← Laws.assoc (tensor .conj (ofTerm f) (ofTerm g)),Laws.tensor_comp]

end Rules
end DosenPetric.Reduced.Gentzen
