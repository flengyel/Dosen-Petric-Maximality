module

public import DosenPetric.GentzenInverseContextAssociativity

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace PrincipalDisjunction
variable {Γ Θ Ξ Δ Λ Ω : List (NormalForm P)} {A B : NormalForm P}

/-- Cut B first, then move the surviving A tag to the second component cut. -/
def reduction (f : G P Γ (A :: B :: Δ))
    (g : G P (A :: Θ) Λ) (h : G P (B :: Ξ) Ω) :
    G P ((Θ ++ Ξ) ++ Γ) ((Λ ++ Ω) ++ Δ) :=
  (ExchangeScript.appendAssoc Λ Ω Δ).inverse.right
    ((ExchangeScript.appendAssoc Θ Ξ Γ).inverse.left
      (G.cut ((HeadRouting.front Ω Δ A).right
        (G.cut ((HeadRouting.front [A] Δ B).right f) h)) g))

def normal (f : G P Γ (A :: B :: Δ))
    (g : G P (A :: Θ) Λ) (h : G P (B :: Ξ) Ω) :
    Hom (ante ((Θ ++ Ξ) ++ Γ)) (succ ((Λ ++ Ω) ++ Δ)) :=
  comp (ofTerm (append .conj (Θ ++ Ξ) Γ).invTerm)
    (comp (tensor .conj (ofTerm (append .conj Θ Ξ).invTerm) (id (ante Γ)))
      (comp (assocL .conj (ante Θ) (ante Ξ) (ante Γ))
        (comp (splice
          (comp (splice (comp (ofTerm f.denote) (frontTwo A B (succ Δ))) (ofTerm h.denote))
            (frontTwo (succ Ω) A (succ Δ))) (ofTerm g.denote))
          (comp (assocR .disj (succ Λ) (succ Ω) (succ Δ))
            (comp (tensor .disj (ofTerm (append .disj Λ Ω).toTerm) (id (succ Δ)))
              (ofTerm (append .disj (Λ ++ Ω) Δ).toTerm))))))

theorem reduction_denote (f : G P Γ (A :: B :: Δ))
    (g : G P (A :: Θ) Λ) (h : G P (B :: Ξ) Ω) :
    ofTerm (reduction f g h).denote = normal f g h := by
  unfold reduction
  rw [ExchangeScript.right_denote, ExchangeScript.left_denote, cut_splice,
    ExchangeScript.right_denote, cut_splice, ExchangeScript.right_denote,
    ]
  have hs : (HeadRouting.front [A] Δ B).arrow .disj = frontTwo A B (succ Δ) :=
    HeadRouting.front_singleton .disj A B Δ
  rw [hs]
  have hf : comp (ofTerm (append .disj Ω (A :: Δ)).toTerm)
      ((HeadRouting.front Ω Δ A).arrow .disj) =
      comp (frontTwo (succ Ω) A (succ Δ))
        (tensor .disj (id A) (ofTerm (append .disj Ω Δ).toTerm)) := by
    have he := HeadRouting.front_split .disj Ω Δ A
    dsimp only [side, category, opposite, split] at he
    exact he
  simp only [Laws.assoc]
  rw [hf, Splice.input]
  rw [← Laws.assoc (splice (comp (ofTerm f.denote) (frontTwo A B (succ Δ))) (ofTerm h.denote)),
    Splice.residual]
  simp only [Laws.assoc]
  have hi := split_assoc_inverse .conj Θ Ξ Γ
  have ho := split_assoc_inverse .disj Λ Ω Δ
  dsimp only [side, category, opposite, sideM, conjMonoidal, disjMonoidal, split] at hi ho
  unfold normal
  have hei := congrArg (fun k => comp k
    (comp (splice
      (comp (splice (comp (ofTerm f.denote) (frontTwo A B (succ Δ))) (ofTerm h.denote))
        (frontTwo (succ Ω) A (succ Δ))) (ofTerm g.denote))
      (comp (tensor .disj (id (succ Λ)) (ofTerm (append .disj Ω Δ).toTerm))
        (comp (ofTerm (append .disj Λ (Ω ++ Δ)).toTerm)
          ((ExchangeScript.appendAssoc Λ Ω Δ).inverse.arrow .disj))))) hi
  simp only [Laws.assoc] at hei
  refine hei.trans ?_
  have heo := congrArg (fun k => comp (ofTerm (append .conj (Θ ++ Ξ) Γ).invTerm)
    (comp (tensor .conj (ofTerm (append .conj Θ Ξ).invTerm) (id (ante Γ)))
      (comp (assocL .conj (ante Θ) (ante Ξ) (ante Γ))
        (comp (splice
          (comp (splice (comp (ofTerm f.denote) (frontTwo A B (succ Δ))) (ofTerm h.denote))
            (frontTwo (succ Ω) A (succ Δ))) (ofTerm g.denote)) k)))) ho
  simpa only [Laws.assoc] using heo

/-- Denotation of the actual native principal disjunction cut. -/
theorem principal_denote (f : G P Γ (A :: B :: Δ))
    (g : G P (A :: Θ) Λ) (h : G P (B :: Ξ) Ω) :
    ofTerm (G.cut (G.disjR Γ [] Δ A B f) (G.disjL g h)).denote = normal f g h := by
  have hg : ofTerm (G.disjL g h).denote =
      comp (tensor .conj (id (.disj A B)) (ofTerm (append .conj Θ Ξ).invTerm))
        (comp (binaryInput (ofTerm g.denote) (ofTerm h.denote))
          (ofTerm (append .disj Λ Ω).toTerm)) := by
    simp only [G.denote_disjL, Rules.disjLeft, binaryInput, ofTerm_comp,
      ofTerm_tensor, ofTerm_id, term_swap, Laws.assoc]
    rw [← Laws.tensor_comp]
    simp only [Laws.assoc]
  rw [cut_splice, G.denote_disjR, disjRight_head, hg, Splice.context, Splice.output, equation]
  simp only [normal, Laws.assoc]

/-- The actual principal disjunction cut equals the two component cuts. -/
theorem rule_equation (f : G P Γ (A :: B :: Δ))
    (g : G P (A :: Θ) Λ) (h : G P (B :: Ξ) Ω) :
    ofTerm (G.cut (G.disjR Γ [] Δ A B f) (G.disjL g h)).denote =
      ofTerm (reduction f g h).denote :=
  (principal_denote f g h).trans (reduction_denote f g h).symm

end PrincipalDisjunction
end DosenPetric.Reduced.Gentzen
