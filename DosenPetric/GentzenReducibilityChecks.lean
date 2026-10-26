module

public import DosenPetric.GentzenReducibility
public import DosenPetric.GentzenSingletonRightRegression
public import DosenPetric.GentzenReducibleExamples

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.ReducibilityChecks
universe u
variable {P : Type u}

/-- The full theorem yields an actual repair of the inhabited Empty-variable
singleton-parametric right-W4 regression, rather than only a classifier. -/
theorem singleton_actual_repair :
    ∃ h : G Empty [.bot] [SingletonRightRegression.C], h.CutFree ∧
      ofTerm h.denote=ofTerm SingletonRightRegression.old.denote := by
  obtain ⟨h,hc,he,_⟩:=reducibility_right
    SingletonRightRegression.old SingletonRightRegression.other SingletonRightRegression.old
    (.here _ []) ProofAddress.root SingletonRightRegression.old_reducible
  exact ⟨h,hc,he⟩

theorem literal_left (l : Literal P) :
    ∃ h : G P [.lit l] [.lit l], h.CutFree ∧
      ofTerm h.denote=ofTerm (ReducibleExamples.left l).denote := by
  obtain ⟨h,hc,he,_⟩:=reducibility_left (G.identity l) (ReducibleExamples.left l)
    (ReducibleExamples.left l) (.here _ []) ProofAddress.root (ReducibleExamples.left_reducible l)
  exact ⟨h,hc,he⟩

theorem literal_right (l : Literal P) :
    ∃ h : G P [.lit l] [.lit l], h.CutFree ∧
      ofTerm h.denote=ofTerm (ReducibleExamples.right l).denote := by
  obtain ⟨h,hc,he,_⟩:=reducibility_right (ReducibleExamples.right l) (G.identity l)
    (ReducibleExamples.right l) (.here _ []) ProofAddress.root (ReducibleExamples.right_reducible l)
  exact ⟨h,hc,he⟩

/-- Equal-label block exchange is not the identity on occurrence positions. -/
theorem equal_label_swap (C : NormalForm P) :
    ((At.here C [C,C]).swapBlocks [] [C,C] [C] []).index=1 ∧
    ((At.there (At.here C [C])).swapBlocks [] [C,C] [C] []).index=2 ∧
    ((At.there (At.there (At.here C []))).swapBlocks [] [C,C] [C] []).index=0 := by
  exact ⟨rfl,rfl,rfl⟩

/-- Every selection regime, including a moving retained copy, is supplied by
an actual proof of the unrestricted factor theorem. -/
theorem crossing_factor (C : NormalForm P) :
    ∃ (K : List (NormalForm P))
      (p : ContractionSelection C ([]++[C,C]++[C]++[]) K)
      (r : ExchangeScript P [C,C] K),
      p.arity=2 ∧ r.get p.keep=At.there (At.here C []) ∧
      ∀ {A : NormalForm P} (a : At ([]++[C,C]++[C]++[]) A),
        (ContractionSelection.more (.fixed C (.last []))).route.get
          (a.swapBlocks [] [C,C] [C] [])=r.get (p.route.get a) :=
  UnrestrictedExchange.factor (Γ:=[]) (X:=[C,C]) (Y:=[C]) (Θ:=[])
    (.more (.fixed C (.last [])))
end DosenPetric.Reduced.Gentzen.ReducibilityChecks
