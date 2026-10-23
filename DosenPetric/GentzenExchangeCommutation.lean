module

public import DosenPetric.GentzenOppositeExchangeRank
public import DosenPetric.GentzenProofInterfaces

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

/- The two opposite-side exchange instances of source (W 1). -/
namespace W1.Exchange

section Left
variable (C : NormalForm P) (gs : List (List (NormalForm P)))
  (Θ Δ X Y Λ : List (NormalForm P)) (hn : 2 ≤ gs.length)
  (f : G P (repeated C gs ++ Θ) (Δ ++ X ++ Y ++ Λ))

def oldL : G P (gaps gs ++ C :: Θ) (Δ ++ Y ++ X ++ Λ) :=
  G.contractL C gs Θ (Δ ++ Y ++ X ++ Λ) hn (G.exchangeR _ Δ X Y Λ f)

def innerL : G P (gaps gs ++ C :: Θ) (Δ ++ X ++ Y ++ Λ) :=
  G.contractL C gs Θ (Δ ++ X ++ Y ++ Λ) hn f

def newL : G P (gaps gs ++ C :: Θ) (Δ ++ Y ++ X ++ Λ) :=
  G.exchangeR _ Δ X Y Λ (innerL C gs Θ Δ X Y Λ hn f)

theorem denoteL : ofTerm (newL C gs Θ Δ X Y Λ hn f).denote =
    ofTerm (oldL C gs Θ Δ X Y Λ hn f).denote := by
  simp only [newL,innerL,oldL,G.denote,ofTerm_comp]
  exact Laws.assoc _ _ _

theorem cutCountL : (newL C gs Θ Δ X Y Λ hn f).cutCount =
    (oldL C gs Θ Δ X Y Λ hn f).cutCount := rfl

theorem cutFreeL : (newL C gs Θ Δ X Y Λ hn f).CutFree ↔
    (oldL C gs Θ Δ X Y Λ hn f).CutFree := Iff.rfl

theorem atomizedL : (newL C gs Θ Δ X Y Λ hn f).Atomized ↔
    (oldL C gs Θ Δ X Y Λ hn f).Atomized := Iff.rfl

theorem newL_atomized (hf : f.Atomized) :
    (newL C gs Θ Δ X Y Λ hn f).Atomized := hf

theorem relationL : (newL C gs Θ Δ X Y Λ hn f).relation =
    (oldL C gs Θ Δ X Y Λ hn f).relation :=
  congrArg occurrenceMap (denoteL C gs Θ Δ X Y Λ hn f)

end Left

section Right
variable (C : NormalForm P) (gs : List (List (NormalForm P)))
  (Γ X Y Θ Λ : List (NormalForm P)) (hn : 2 ≤ gs.length)
  (f : G P (Γ ++ X ++ Y ++ Θ) (repeated C gs ++ Λ))

def oldR : G P (Γ ++ Y ++ X ++ Θ) (gaps gs ++ C :: Λ) :=
  G.contractR (Γ ++ Y ++ X ++ Θ) C gs Λ hn (G.exchangeL Γ X Y Θ _ f)

def innerR : G P (Γ ++ X ++ Y ++ Θ) (gaps gs ++ C :: Λ) :=
  G.contractR (Γ ++ X ++ Y ++ Θ) C gs Λ hn f

def newR : G P (Γ ++ Y ++ X ++ Θ) (gaps gs ++ C :: Λ) :=
  G.exchangeL Γ X Y Θ _ (innerR C gs Γ X Y Θ Λ hn f)

theorem denoteR : ofTerm (newR C gs Γ X Y Θ Λ hn f).denote =
    ofTerm (oldR C gs Γ X Y Θ Λ hn f).denote := by
  simp only [newR,innerR,oldR,G.denote,ofTerm_comp]
  exact (Laws.assoc _ _ _).symm

theorem cutCountR : (newR C gs Γ X Y Θ Λ hn f).cutCount =
    (oldR C gs Γ X Y Θ Λ hn f).cutCount := rfl

theorem cutFreeR : (newR C gs Γ X Y Θ Λ hn f).CutFree ↔
    (oldR C gs Γ X Y Θ Λ hn f).CutFree := Iff.rfl

theorem atomizedR : (newR C gs Γ X Y Θ Λ hn f).Atomized ↔
    (oldR C gs Γ X Y Θ Λ hn f).Atomized := Iff.rfl

theorem newR_atomized (hf : f.Atomized) :
    (newR C gs Γ X Y Θ Λ hn f).Atomized := hf

theorem relationR : (newR C gs Γ X Y Θ Λ hn f).relation =
    (oldR C gs Γ X Y Θ Λ hn f).relation :=
  congrArg occurrenceMap (denoteR C gs Γ X Y Θ Λ hn f)

end Right
end W1.Exchange
end DosenPetric.Reduced.Gentzen
