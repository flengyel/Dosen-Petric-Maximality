module

public import DosenPetric.GentzenMaskLogicalPositions

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.SelectionMask
universe u
variable {P : Type u} {C : NormalForm P} {Γ Θ : List (NormalForm P)}
variable (g : SelectionMask C Γ) (t : SelectionMask C Θ) (o : Op) (A B : NormalForm P)

theorem context_logical_surviving {E : NormalForm P} (a : At (Γ++A::B::Θ) E)
    (b : At (Γ++o.formula A B::Θ) E)
    (hp : At.fixed Γ [A,B] [o.formula A B] Θ a=some b) :
    (side P o).comp
      ((side P o).comp ((contextCanonical g t [o.formula A B]).sideArrow o) (logicalSide o Γ Θ A B))
      (component o a)=
    (side P o).comp
      ((side P o).comp (logicalSide o (C::g.erased) t.erased A B)
        ((contextCanonical g t [A,B]).sideArrow o)) (component o a) := by
  have hs:=context_parent g t A B (o.formula A B) a
  rw [hp,Option.map_some] at hs
  rw [(side P o).assoc,logical_survives o Γ Θ A B a b hp,Route.sideArrow_get,
    (side P o).assoc,Route.sideArrow_get,
    logical_survives o (C::g.erased) t.erased A B _ _ hs.symm]

/-- Naturality at arbitrary fixed context selections, proved by product or
coproduct components, including the two consumed logical components. -/
theorem context_logical_square :
    (side P o).comp ((contextCanonical g t [o.formula A B]).sideArrow o) (logicalSide o Γ Θ A B)=
      (side P o).comp (logicalSide o (C::g.erased) t.erased A B)
        ((contextCanonical g t [A,B]).sideArrow o) := by
  have hd : (contextCanonical g t [o.formula A B]).get (At.shift Γ (.here (o.formula A B) Θ))=
      At.shift (C::g.erased) (.here (o.formula A B) t.erased) := by
    simpa only [At.before,List.nil_append] using context_middle g t [o.formula A B] (.here (o.formula A B) [])
  have ha : (contextCanonical g t [A,B]).get (At.shift Γ (.here A (B::Θ)))=
      At.shift (C::g.erased) (.here A (B::t.erased)) := by
    simpa only [At.before,List.singleton_append] using context_middle g t [A,B] (.here A [B])
  have hb : (contextCanonical g t [A,B]).get (At.shift Γ (.there (.here B Θ)))=
      At.shift (C::g.erased) (.there (.here B t.erased)) := by
    simpa only [At.before,List.nil_append] using context_middle g t [A,B] (.there (.here B []))
  apply side_ext o
  intro E a
  cases At.cases_append Γ ([A,B]++Θ) a with
  | inl h=>
    obtain ⟨a,rfl⟩:=h
    exact context_logical_surviving g t o A B _ _ (At.fixed_before ..)
  | inr h=>
    obtain ⟨a,rfl⟩:=h
    cases At.cases_append [A,B] Θ a with
    | inr h=>
      obtain ⟨a,rfl⟩:=h
      exact context_logical_surviving g t o A B _ _ (At.fixed_tail ..)
    | inl h=>
      obtain ⟨a,rfl⟩:=h
      cases a with
      | here=>
        simp only [At.before,List.singleton_append]
        rw [(side P o).assoc,logical_first o Γ Θ A B,←(side P o).assoc,Route.sideArrow_get]
        rw [hd]
        rw [(side P o).assoc,Route.sideArrow_get,ha,logical_first o (C::g.erased) t.erased A B]
      | there a=>
        cases a with
        | there a=>cases a
        | here=>
          simp only [At.before,List.nil_append]
          rw [(side P o).assoc,logical_second o Γ Θ A B,←(side P o).assoc,Route.sideArrow_get]
          rw [hd]
          rw [(side P o).assoc,Route.sideArrow_get,hb,logical_second o (C::g.erased) t.erased A B]
end DosenPetric.Reduced.Gentzen.SelectionMask
