module

public import DosenPetric.GentzenOppositeLogicalRank
public import DosenPetric.GentzenProofInterfaces

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

/- The two opposite-side unary logical instances of source (W 1). -/
namespace W1.Logical

section Left
variable (A B C : NormalForm P) (gs : List (List (NormalForm P)))
  (Θ Δ Λ : List (NormalForm P)) (hn : 2 ≤ gs.length)
  (f : G P (repeated C gs ++ Θ) (Δ ++ A :: B :: Λ))

def oldL : G P (gaps gs ++ C :: Θ) (Δ ++ .disj A B :: Λ) :=
  G.contractL C gs Θ (Δ ++ .disj A B :: Λ) hn (G.disjR _ Δ Λ A B f)

def innerL : G P (gaps gs ++ C :: Θ) (Δ ++ A :: B :: Λ) :=
  G.contractL C gs Θ (Δ ++ A :: B :: Λ) hn f

def newL : G P (gaps gs ++ C :: Θ) (Δ ++ .disj A B :: Λ) :=
  G.disjR _ Δ Λ A B (innerL A B C gs Θ Δ Λ hn f)

theorem denoteL : ofTerm (newL A B C gs Θ Δ Λ hn f).denote =
    ofTerm (oldL A B C gs Θ Δ Λ hn f).denote := by
  simp only [newL,innerL,oldL,G.denote,ofTerm_comp]
  exact Laws.assoc _ _ _

theorem cutCountL : (newL A B C gs Θ Δ Λ hn f).cutCount =
    (oldL A B C gs Θ Δ Λ hn f).cutCount := rfl

theorem cutFreeL : (newL A B C gs Θ Δ Λ hn f).CutFree ↔
    (oldL A B C gs Θ Δ Λ hn f).CutFree := Iff.rfl

theorem atomizedL : (newL A B C gs Θ Δ Λ hn f).Atomized ↔
    (oldL A B C gs Θ Δ Λ hn f).Atomized := Iff.rfl

theorem newL_atomized (hf : f.Atomized) :
    (newL A B C gs Θ Δ Λ hn f).Atomized := hf

theorem relationL : (newL A B C gs Θ Δ Λ hn f).relation =
    (oldL A B C gs Θ Δ Λ hn f).relation :=
  congrArg occurrenceMap (denoteL A B C gs Θ Δ Λ hn f)

end Left

section Right
variable (A B C : NormalForm P) (gs : List (List (NormalForm P)))
  (Γ Θ Λ : List (NormalForm P)) (hn : 2 ≤ gs.length)
  (f : G P (Γ ++ A :: B :: Θ) (repeated C gs ++ Λ))

def oldR : G P (Γ ++ .conj A B :: Θ) (gaps gs ++ C :: Λ) :=
  G.contractR (Γ ++ .conj A B :: Θ) C gs Λ hn (G.conjL Γ Θ _ A B f)

def innerR : G P (Γ ++ A :: B :: Θ) (gaps gs ++ C :: Λ) :=
  G.contractR (Γ ++ A :: B :: Θ) C gs Λ hn f

def newR : G P (Γ ++ .conj A B :: Θ) (gaps gs ++ C :: Λ) :=
  G.conjL Γ Θ _ A B (innerR A B C gs Γ Θ Λ hn f)

theorem denoteR : ofTerm (newR A B C gs Γ Θ Λ hn f).denote =
    ofTerm (oldR A B C gs Γ Θ Λ hn f).denote := by
  simp only [newR,innerR,oldR,G.denote,ofTerm_comp]
  exact (Laws.assoc _ _ _).symm

theorem cutCountR : (newR A B C gs Γ Θ Λ hn f).cutCount =
    (oldR A B C gs Γ Θ Λ hn f).cutCount := rfl

theorem cutFreeR : (newR A B C gs Γ Θ Λ hn f).CutFree ↔
    (oldR A B C gs Γ Θ Λ hn f).CutFree := Iff.rfl

theorem atomizedR : (newR A B C gs Γ Θ Λ hn f).Atomized ↔
    (oldR A B C gs Γ Θ Λ hn f).Atomized := Iff.rfl

theorem newR_atomized (hf : f.Atomized) :
    (newR A B C gs Γ Θ Λ hn f).Atomized := hf

theorem relationR : (newR A B C gs Γ Θ Λ hn f).relation =
    (oldR A B C gs Γ Θ Λ hn f).relation :=
  congrArg occurrenceMap (denoteR A B C gs Γ Θ Λ hn f)

end Right
end W1.Logical
end DosenPetric.Reduced.Gentzen
