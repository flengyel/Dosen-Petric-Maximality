module

public import DosenPetric.GentzenTripleContexts

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace PrincipalConjunction
variable {Γ Θ Δ Λ Ξ Ω : List (NormalForm P)} {A B : NormalForm P}

/-- The two component cuts, transported to the original output sequent. -/
def reduction (f : G P Γ (A :: Δ)) (g : G P Θ (B :: Λ))
    (h : G P (A :: B :: Ξ) Ω) : G P (Ξ ++ (Γ ++ Θ)) (Ω ++ (Δ ++ Λ)) :=
  (ExchangeScript.appendAssoc Ω Δ Λ).right
    ((ExchangeScript.appendAssoc Ξ Γ Θ).left (G.cut g (G.cut f h)))

/-- The denotation of the two smaller cuts with all fold comparisons explicit. -/
theorem reduction_denote (f : G P Γ (A :: Δ)) (g : G P Θ (B :: Λ))
    (h : G P (A :: B :: Ξ) Ω) :
    ofTerm (reduction f g h).denote =
      comp (splitThree .conj Ξ Γ Θ)
        (comp (splice (ofTerm g.denote)
            (comp (assocR .conj B (ante Ξ) (ante Γ)) (splice (ofTerm f.denote) (ofTerm h.denote))))
          (splitThree .disj Ω Δ Λ)) := by
  unfold reduction
  rw [ExchangeScript.right_denote, ExchangeScript.left_denote, cut_splice, cut_splice]
  have hc : ofTerm (append .conj (B :: Ξ) Γ).invTerm =
      comp (tensor .conj (id B) (ofTerm (append .conj Ξ Γ).invTerm))
        (assocR .conj B (ante Ξ) (ante Γ)) := split_cons .conj B Ξ Γ
  rw [hc]
  simp only [Laws.assoc]
  rw [Splice.context, ← Laws.assoc (assocR .conj B (ante Ξ) (ante Γ)), Splice.output]
  simp only [Laws.assoc]
  have hi : comp ((ExchangeScript.appendAssoc Ξ Γ Θ).arrow .conj)
      (comp (ofTerm (append .conj (Ξ ++ Γ) Θ).invTerm)
        (tensor .conj (ofTerm (append .conj Ξ Γ).invTerm) (id (ante Θ)))) =
      splitThree .conj Ξ Γ Θ := by
    rw [splitThree_eq]
    exact split_assoc .conj Ξ Γ Θ
  have ho : comp (tensor .disj (ofTerm (append .disj Ω Δ).toTerm) (id (succ Λ)))
      (comp (ofTerm (append .disj (Ω ++ Δ) Λ).toTerm)
        ((ExchangeScript.appendAssoc Ω Δ Λ).arrow .disj)) = splitThree .disj Ω Δ Λ := by
    rw [splitThree_eq]
    have he := split_assoc .disj Ω Δ Λ
    dsimp only [side, category, opposite, sideM, disjMonoidal, split] at he ⊢
    simpa only [Laws.assoc] using he
  rw [ho]
  have he := congrArg (fun k => comp k
    (comp (splice (ofTerm g.denote)
      (comp (assocR .conj B (ante Ξ) (ante Γ)) (splice (ofTerm f.denote) (ofTerm h.denote))))
      (splitThree .disj Ω Δ Λ))) hi
  simpa only [Laws.assoc] using he

theorem principal_denote (f : G P Γ (A :: Δ)) (g : G P Θ (B :: Λ))
    (h : G P (A :: B :: Ξ) Ω) :
    ofTerm (G.cut (G.conjR f g) (G.conjL [] Ξ Ω A B h)).denote =
      comp (splitThree .conj Ξ Γ Θ)
        (comp (splice (ofTerm g.denote)
            (comp (assocR .conj B (ante Ξ) (ante Γ)) (splice (ofTerm f.denote) (ofTerm h.denote))))
          (splitThree .disj Ω Δ Λ)) := by
  have hf : ofTerm (G.conjR f g).denote =
      comp (ofTerm (append .conj Γ Θ).invTerm)
        (comp (comp (tensor .conj (ofTerm f.denote) (ofTerm g.denote))
            (ofTerm (Term.mixedDisj A (succ Δ) B (succ Λ))))
          (tensor .disj (id (.conj A B)) (ofTerm (append .disj Δ Λ).toTerm))) := by
    simp only [G.denote_conjR, Rules.conjRight, ofTerm_comp, ofTerm_tensor,
      ofTerm_id, Laws.assoc]
  rw [cut_splice, hf, G.denote_conjL, conjLeft_head, Splice.input, Splice.residual,
    PrincipalConjunction.equation]
  simp only [Laws.assoc]
  have ho : comp (assocL .disj (succ Ω) (succ Δ) (succ Λ))
      (comp (tensor .disj (id (succ Ω)) (ofTerm (append .disj Δ Λ).toTerm))
        (ofTerm (append .disj Ω (Δ ++ Λ)).toTerm)) = splitThree .disj Ω Δ Λ := by
    rw [splitThree_eq]
    exact (Laws.assoc ..).symm
  rw [ho]
  have hi : comp (ofTerm (append .conj Ξ (Γ ++ Θ)).invTerm)
      (comp (tensor .conj (id (ante Ξ)) (ofTerm (append .conj Γ Θ).invTerm))
        (assocR .conj (ante Ξ) (ante Γ) (ante Θ))) = splitThree .conj Ξ Γ Θ := by
    rw [splitThree_eq]
    rfl
  have he := congrArg (fun k => comp k
    (comp (splice (ofTerm g.denote)
      (comp (assocR .conj B (ante Ξ) (ante Γ)) (splice (ofTerm f.denote) (ofTerm h.denote))))
      (splitThree .disj Ω Δ Λ))) hi
  simpa only [Laws.assoc] using he

/-- The actual principal conjunction cut equals the two smaller-formula cuts. -/
theorem rule_equation (f : G P Γ (A :: Δ)) (g : G P Θ (B :: Λ))
    (h : G P (A :: B :: Ξ) Ω) :
    ofTerm (G.cut (G.conjR f g) (G.conjL [] Ξ Ω A B h)).denote =
      ofTerm (reduction f g h).denote :=
  (principal_denote f g h).trans (reduction_denote f g h).symm

end PrincipalConjunction
end DosenPetric.Reduced.Gentzen
