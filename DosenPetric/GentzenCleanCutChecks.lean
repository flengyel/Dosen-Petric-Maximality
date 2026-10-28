module

public import DosenPetric.GentzenCleanCuts
public import DosenPetric.GentzenAtomizationBlockedBoundary

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.CleanCutChecks
universe u
variable {P : Type u}

theorem compound_identity (A B : NormalForm P) :
    ∃ t : StructuralProgram P [.conj A B] [.conj A B], t.Atomic ∧
      ∀ {D : NormalForm P} (a : At [.conj A B] D), t.get a = a := by
  obtain ⟨t,ht,hg⟩ := (Route.identity [.conj A B]).atomic_program
    (fun a ha => False.elim (ha ⟨a,Route.get_identity a⟩))
  exact ⟨t,ht,fun a => (hg a).trans (Route.get_identity a)⟩

theorem old_empty_compound_not_atomic (A B : NormalForm P) :
    ¬ (StructuralProgram.empty [.conj A B]).Atomic := by
  intro h
  exact h.1

def doubled (D : NormalForm P) : Route [D] [D,D] :=
  .cons (.here D []) (.cons (.here D []) .nil)

theorem doubled_atomic_program (D : NormalForm P) :
    ∃ t : StructuralProgram P [D] [D,D], t.Atomic ∧
      ∀ {A : NormalForm P} (a : At [D,D] A), t.get a = (doubled D).get a := by
  apply (doubled D).atomic_program
  intro A a ha
  cases a with
  | here => exact False.elim (ha ⟨.here D [D],rfl⟩)
  | there a => cases a

/-- Using the first compound occurrence leaves the second tag unsupported. -/
theorem equal_compound_unused (A B : NormalForm P) :
    ¬ (Route.cons (.here (.conj A B) [.conj A B]) .nil).AtomicOmissions := by
  intro h
  apply h (.there (.here (.conj A B) []))
  rintro ⟨b,hb⟩
  cases b with
  | here => cases hb
  | there b => cases b

theorem empty_atomic_context :
    ∃ t : StructuralProgram Empty [.top,.bot] [], t.Atomic := by
  obtain ⟨t,ht,_⟩ := (Route.nil : Route [.top,.bot] []).atomic_program (by
    intro A a _
    cases a with
    | here => trivial
    | there a => cases a with
      | here => trivial
      | there a => cases a)
  exact ⟨t,ht⟩

theorem empty_route :
    ∃ t : StructuralProgram Empty [] [], t.Atomic :=
  ⟨.identity [],True.intro⟩

theorem signed_omission (l : Literal P) :
    (Route.nil : Route [.lit l] []).AtomicOmissions := by
  intro A a _
  cases a with
  | here => trivial
  | there a => cases a

def equalExchange : Route [NormalForm.disj (.top : NormalForm Empty) .bot,
    .disj .top .bot] [.disj .top .bot,.disj .top .bot] :=
  Route.exchange [] [.disj .top .bot] [.disj .top .bot] []

theorem equal_exchange_tags :
    (equalExchange.get (.here _ [_])).index = 1 ∧
    (equalExchange.get (.there (.here _ []))).index = 0 := by decide

theorem equal_exchange_atomic : equalExchange.AtomicOmissions :=
  Route.exchange_atomicOmissions [] [_] [_] []

/-- The negative preservation example has a positive simultaneous representative. -/
theorem boundary_clean :
    ∃ (f' : G Empty [] [.top])
      (g' : G Empty [.top,AtomizationBlockedBoundary.insertedFormula] [.top]),
      G.Topmost f' g' ∧ f'.Atomized ∧ g'.Atomized ∧
      ofTerm f'.denote = ofTerm G.topI.denote ∧
      ofTerm g'.denote = ofTerm AtomizationBlockedBoundary.before.denote ∧
      AllBlockedR f' ∧ AllBlockedL g' :=
  clean_cut_premises G.topI AtomizationBlockedBoundary.before ⟨rfl,rfl⟩

end DosenPetric.Reduced.Gentzen.CleanCutChecks
