module

public import DosenPetric.GentzenOppositeContractionRank
public import DosenPetric.GentzenProofInterfaces

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.W1.Contraction
universe u
variable {P : Type u}
variable (C D : NormalForm P) (gs hs : List (List (NormalForm P)))
  (Θ Λ : List (NormalForm P)) (hn : 2 ≤ gs.length) (hm : 2 ≤ hs.length)
  (f : G P (repeated C gs ++ Θ) (repeated D hs ++ Λ))

def innerL : G P (gaps gs ++ C :: Θ) (repeated D hs ++ Λ) :=
  G.contractL C gs Θ (repeated D hs ++ Λ) hn f

def innerR : G P (repeated C gs ++ Θ) (gaps hs ++ D :: Λ) :=
  G.contractR (repeated C gs ++ Θ) D hs Λ hm f

def outerL : G P (gaps gs ++ C :: Θ) (gaps hs ++ D :: Λ) :=
  G.contractL C gs Θ (gaps hs ++ D :: Λ) hn (innerR C D gs hs Θ Λ hm f)

def outerR : G P (gaps gs ++ C :: Θ) (gaps hs ++ D :: Λ) :=
  G.contractR (gaps gs ++ C :: Θ) D hs Λ hm (innerL C D gs hs Θ Λ hn f)

/-- One commuting pair, with execution-order composition. -/
theorem denote : ofTerm (outerR C D gs hs Θ Λ hn hm f).denote =
    ofTerm (outerL C D gs hs Θ Λ hn hm f).denote := by
  simp only [outerR,outerL,innerL,innerR,G.denote,ofTerm_comp]
  exact Laws.assoc _ _ _

theorem denote_reverse : ofTerm (outerL C D gs hs Θ Λ hn hm f).denote =
    ofTerm (outerR C D gs hs Θ Λ hn hm f).denote := (denote ..).symm

theorem cutCount : (outerR C D gs hs Θ Λ hn hm f).cutCount =
    (outerL C D gs hs Θ Λ hn hm f).cutCount := rfl

theorem cutFree : (outerR C D gs hs Θ Λ hn hm f).CutFree ↔
    (outerL C D gs hs Θ Λ hn hm f).CutFree := Iff.rfl

theorem atomized : (outerR C D gs hs Θ Λ hn hm f).Atomized ↔
    (outerL C D gs hs Θ Λ hn hm f).Atomized := Iff.rfl

theorem relation : (outerR C D gs hs Θ Λ hn hm f).relation =
    (outerL C D gs hs Θ Λ hn hm f).relation :=
  congrArg occurrenceMap (denote C D gs hs Θ Λ hn hm f)

/-- Aliases for the existing selected ranks of the two inner contractions. -/
def leftRank : Nat := G.contractionRankL C gs Θ (repeated D hs ++ Λ) hn f

def rightRank : Nat := G.contractionRankR (repeated C gs ++ Θ) D hs Λ hm f

/-- Sum of just the two displayed final-position cluster ranks. -/
def endpointSum (g : G P (gaps gs ++ C :: Θ) (gaps hs ++ D :: Λ)) : Nat :=
  g.rho .left (At.shift (gaps gs) (.here C Θ)) +
    g.rho .right (At.shift (gaps hs) (.here D Λ))

end DosenPetric.Reduced.Gentzen.W1.Contraction
