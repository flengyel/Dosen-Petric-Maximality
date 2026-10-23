module

public import DosenPetric.GentzenOppositeThinningRank
public import DosenPetric.GentzenProofInterfaces

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

/- The two opposite-side thinning instances of source (W 1). -/
namespace W1

section Left
variable (C D : NormalForm P) (gs : List (List (NormalForm P)))
  (Θ Δ Λ : List (NormalForm P)) (hn : 2 ≤ gs.length)
  (f : G P (repeated C gs ++ Θ) (Δ ++ Λ))

def oldL : G P (gaps gs ++ C :: Θ) (Δ ++ D :: Λ) :=
  G.contractL C gs Θ (Δ ++ D :: Λ) hn (G.thinR _ Δ Λ D f)

def innerL : G P (gaps gs ++ C :: Θ) (Δ ++ Λ) :=
  G.contractL C gs Θ (Δ ++ Λ) hn f

def newL : G P (gaps gs ++ C :: Θ) (Δ ++ D :: Λ) :=
  G.thinR _ Δ Λ D (innerL C gs Θ Δ Λ hn f)

theorem denoteL : ofTerm (newL C D gs Θ Δ Λ hn f).denote =
    ofTerm (oldL C D gs Θ Δ Λ hn f).denote := by
  simp only [newL,innerL,oldL,G.denote,ofTerm_comp]
  exact Laws.assoc _ _ _

theorem cutCountL : (newL C D gs Θ Δ Λ hn f).cutCount =
    (oldL C D gs Θ Δ Λ hn f).cutCount := rfl

theorem cutFreeL : (newL C D gs Θ Δ Λ hn f).CutFree ↔
    (oldL C D gs Θ Δ Λ hn f).CutFree := Iff.rfl

theorem atomizedL : (newL C D gs Θ Δ Λ hn f).Atomized ↔
    (oldL C D gs Θ Δ Λ hn f).Atomized := Iff.rfl

theorem newL_atomized (hD : AtomicFormula D) (hf : f.Atomized) :
    (newL C D gs Θ Δ Λ hn f).Atomized := ⟨hD,hf⟩

theorem relationL : (newL C D gs Θ Δ Λ hn f).relation =
    (oldL C D gs Θ Δ Λ hn f).relation :=
  congrArg occurrenceMap (denoteL C D gs Θ Δ Λ hn f)

end Left

section Right
variable (C D : NormalForm P) (gs : List (List (NormalForm P)))
  (Γ Θ Λ : List (NormalForm P)) (hn : 2 ≤ gs.length)
  (f : G P (Γ ++ Θ) (repeated C gs ++ Λ))

def oldR : G P (Γ ++ D :: Θ) (gaps gs ++ C :: Λ) :=
  G.contractR (Γ ++ D :: Θ) C gs Λ hn (G.thinL Γ Θ _ D f)

def innerR : G P (Γ ++ Θ) (gaps gs ++ C :: Λ) :=
  G.contractR (Γ ++ Θ) C gs Λ hn f

def newR : G P (Γ ++ D :: Θ) (gaps gs ++ C :: Λ) :=
  G.thinL Γ Θ _ D (innerR C gs Γ Θ Λ hn f)

theorem denoteR : ofTerm (newR C D gs Γ Θ Λ hn f).denote =
    ofTerm (oldR C D gs Γ Θ Λ hn f).denote := by
  simp only [newR,innerR,oldR,G.denote,ofTerm_comp]
  exact (Laws.assoc _ _ _).symm

theorem cutCountR : (newR C D gs Γ Θ Λ hn f).cutCount =
    (oldR C D gs Γ Θ Λ hn f).cutCount := rfl

theorem cutFreeR : (newR C D gs Γ Θ Λ hn f).CutFree ↔
    (oldR C D gs Γ Θ Λ hn f).CutFree := Iff.rfl

theorem atomizedR : (newR C D gs Γ Θ Λ hn f).Atomized ↔
    (oldR C D gs Γ Θ Λ hn f).Atomized := Iff.rfl

theorem newR_atomized (hD : AtomicFormula D) (hf : f.Atomized) :
    (newR C D gs Γ Θ Λ hn f).Atomized := ⟨hD,hf⟩

theorem relationR : (newR C D gs Γ Θ Λ hn f).relation =
    (oldR C D gs Γ Θ Λ hn f).relation :=
  congrArg occurrenceMap (denoteR C D gs Γ Θ Λ hn f)

end Right
end W1
end DosenPetric.Reduced.Gentzen
