module

public import DosenPetric.GentzenReducibilityMixed
public import DosenPetric.GentzenBlockedExamples

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.W5.MixedPremiseMix.Examples
universe u
variable {P : Type u}

abbrev two (C : NormalForm P) := ContractionSelection.ofList C [[],[]] [] (by intro h; cases h)
abbrev three (C : NormalForm P) := ContractionSelection.ofList C [[],[],[]] [] (by intro h; cases h)
theorem independent_arities (C : NormalForm P) : (two C).arity=2 ∧ (three C).arity=3 := ⟨rfl,rfl⟩

def fl : G Empty [.top,.top,.top] [.top] := W1.SameSideLogical.constantLeft _
def gl : G Empty [.top,.top] [.top] := W1.SameSideLogical.constantLeft _
def fr : G Empty [.bot] [.top,.top,.top] := W1.SameSideLogical.constantRight _
def gr : G Empty [.bot] [.top,.top] := W1.SameSideLogical.constantRight _
theorem inhabited_left :
    ofTerm (newL (two .top) (three .top) fl gl).denote =
      ofTerm (oldL (two .top) (three .top) fl gl).denote := denoteL ..
theorem inhabited_right :
    ofTerm (newR (two .top) (three .top) fr gr).denote =
      ofTerm (oldR (two .top) (three .top) fr gr).denote := denoteR ..
theorem inhabited_blocked : BlockedL (newL (two .top) (three .top) fl gl) ∧
    BlockedR (newR (two .top) (three .top) fr gr) := ⟨blockedL ..,blockedR ..⟩
theorem inhabited_cutFree : (newL (two .top) (three .top) fl gl).CutFree ∧
    (newR (two .top) (three .top) fr gr).CutFree := by
  constructor
  · rw [G.CutFree,new_countL]; rfl
  · rw [G.CutFree,new_countR]; rfl

def cutThree (l : Literal P) : G P [.lit l,.lit l,.lit l] [.lit l] :=
  G.thinL [] [.lit l,.lit l] [.lit l] (.lit l)
    (G.thinL [] [.lit l] [.lit l] (.lit l) (G.cut (G.identity l) (G.identity l)))
def cutTwo (l : Literal P) : G P [.lit l,.lit l] [.lit l] :=
  G.thinL [] [.lit l] [.lit l] (.lit l) (G.cut (G.identity l) (G.identity l))
theorem actual_cuts (l : Literal P) :
    (newL (two (.lit l)) (three (.lit l)) (cutThree l) (cutTwo l)).cutCount=2 := by
  rw [new_countL]; rfl
theorem both_signs (p : P) :
    (newL (two (.lit (.pos p))) (three (.lit (.pos p))) (cutThree (.pos p)) (cutTwo (.pos p))).cutCount=2 ∧
    (newL (two (.lit (.neg p))) (three (.lit (.neg p))) (cutThree (.neg p)) (cutTwo (.neg p))).cutCount=2 :=
  ⟨actual_cuts _,actual_cuts _⟩

end DosenPetric.Reduced.Gentzen.W5.MixedPremiseMix.Examples
