module

public import DosenPetric.GentzenProofInterfaces

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.G
universe u
variable {P : Type u}

theorem denote_identity (l : Literal P) :
    ofTerm (G.identity l).denote = comp (rightOut .conj (.lit l))
      (comp (id (.lit l)) (rightIn .disj (.lit l))) := rfl

theorem denote_zero (l : Literal P) :
    ofTerm (G.zero l).denote = comp (rightOut .conj (.lit l))
      (comp (Reduced.zero (.lit l)) (rightIn .disj (.lit l))) := rfl

theorem denote_topI : ofTerm (G.topI (P := P)).denote = rightIn .disj .top := rfl

theorem denote_botE : ofTerm (G.botE (P := P)).denote = rightOut .conj .bot := rfl

theorem denote_exchangeL (Γ X Y Θ Δ : List (NormalForm P)) (f : G P (Γ ++ X ++ Y ++ Θ) Δ) :
    ofTerm (G.exchangeL Γ X Y Θ Δ f).denote =
      comp (ofTerm (exchange .conj Γ X Y Θ).invTerm) (ofTerm f.denote) := rfl

theorem denote_exchangeR (Γ Δ X Y Λ : List (NormalForm P)) (f : G P Γ (Δ ++ X ++ Y ++ Λ)) :
    ofTerm (G.exchangeR Γ Δ X Y Λ f).denote =
      comp (ofTerm f.denote) (ofTerm (exchange .disj Δ X Y Λ).toTerm) := rfl

theorem denote_thinL (Γ Θ Δ : List (NormalForm P)) (A : NormalForm P) (f : G P (Γ ++ Θ) Δ) :
    ofTerm (G.thinL Γ Θ Δ A f).denote = comp (ofTerm (Route.thin Γ Θ A).product) (ofTerm f.denote) := rfl

theorem denote_thinR (Γ Δ Λ : List (NormalForm P)) (A : NormalForm P) (f : G P Γ (Δ ++ Λ)) :
    ofTerm (G.thinR Γ Δ Λ A f).denote = comp (ofTerm f.denote) (ofTerm (Route.thin Δ Λ A).coproduct) := rfl

theorem denote_contractL (C : NormalForm P) (gs : List (List (NormalForm P)))
    (Θ Δ : List (NormalForm P)) (hn : 2 ≤ gs.length) (f : G P (repeated C gs ++ Θ) Δ) :
    ofTerm (G.contractL C gs Θ Δ hn f).denote = comp (ofTerm (copies C gs Θ).product) (ofTerm f.denote) := rfl

theorem denote_contractR (Γ : List (NormalForm P)) (C : NormalForm P) (gs : List (List (NormalForm P)))
    (Λ : List (NormalForm P)) (hn : 2 ≤ gs.length) (f : G P Γ (repeated C gs ++ Λ)) :
    ofTerm (G.contractR Γ C gs Λ hn f).denote = comp (ofTerm f.denote) (ofTerm (copies C gs Λ).coproduct) := rfl

theorem denote_conjL (Γ Θ Δ : List (NormalForm P)) (A B : NormalForm P) (f : G P (Γ ++ A :: B :: Θ) Δ) :
    ofTerm (G.conjL Γ Θ Δ A B f).denote = comp (ofTerm (Rules.conjLeft Γ Θ A B).toTerm) (ofTerm f.denote) := rfl

theorem denote_disjR (Γ Δ Λ : List (NormalForm P)) (A B : NormalForm P) (f : G P Γ (Δ ++ A :: B :: Λ)) :
    ofTerm (G.disjR Γ Δ Λ A B f).denote = comp (ofTerm f.denote) (ofTerm (Rules.disjRight Δ Λ A B).toTerm) := rfl

theorem denote_conjR {Γ Θ Δ Λ : List (NormalForm P)} {A B : NormalForm P}
    (f : G P Γ (A :: Δ)) (g : G P Θ (B :: Λ)) :
    ofTerm (G.conjR f g).denote = ofTerm (Rules.conjRight f.denote g.denote) := rfl

theorem denote_disjL {Γ Θ Δ Λ : List (NormalForm P)} {A B : NormalForm P}
    (f : G P (A :: Γ) Δ) (g : G P (B :: Θ) Λ) :
    ofTerm (G.disjL f g).denote = ofTerm (Rules.disjLeft f.denote g.denote) := rfl

theorem denote_mix {Γ Θ Δ Λ : List (NormalForm P)} (f : G P Γ Δ) (g : G P Θ Λ) :
    ofTerm (G.mix f g).denote = ofTerm (Rules.mix f.denote g.denote) := rfl

theorem denote_cut {Γ Θ Δ Λ : List (NormalForm P)} {C : NormalForm P}
    (f : G P Γ (C :: Δ)) (g : G P (C :: Θ) Λ) :
    ofTerm (G.cut f g).denote =
      comp (ofTerm (append .conj Θ Γ).invTerm)
        (comp (tensor .conj (id (ante Θ)) (ofTerm f.denote))
          (comp (dist (ante Θ) C (succ Δ))
            (comp (tensor .disj (comp (swap .conj (ante Θ) C) (ofTerm g.denote)) (id (succ Δ)))
              (ofTerm (append .disj Λ Δ).toTerm)))) := rfl

/-- The displayed e'-disjunction, expanded into the p.240 steps. -/
theorem sourceDisj_expansion (A B C D : NormalForm P) :
    ofTerm (Term.mixedDisj A C B D) =
      comp (dist (.disj A C) B D)
        (comp (tensor .disj (swap .conj (.disj A C) B) (id D))
          (comp (tensor .disj (dist B A C) (id D))
            (comp (tensor .disj (tensor .disj (swap .conj B A) (id C)) (id D))
              (assocL .disj (.conj A B) C D)))) := by
  change comp (dist (.disj A C) B D)
    (comp (tensor .disj
      (comp (swap .conj (.disj A C) B)
        (comp (dist B A C) (tensor .disj (swap .conj B A) (id C)))) (id D))
      (assocL .disj (.conj A B) C D)) = _
  simp only [← Laws.assoc, Laws.tensor_comp, Laws.id_comp]

end DosenPetric.Reduced.Gentzen.G
