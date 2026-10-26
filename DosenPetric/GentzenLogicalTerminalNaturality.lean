module

public import DosenPetric.GentzenLogicalTerminalRoutes

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

/-- Terminalize one unary logical introduction by its actual block exchanges.
The component calculation uses the different block lengths one and two. -/
theorem logical_terminal_square (o : Op) (Γ Θ : List (NormalForm P)) (A B : NormalForm P) :
    (side P o).comp ((Route.moveEnd Γ [o.formula A B] Θ).sideArrow o) (logicalSide o Γ Θ A B)=
      (side P o).comp (logicalSide o (Γ++Θ) [] A B)
        ((Route.moveEnd Γ [A,B] Θ).sideArrow o) := by
  have hd : (Route.moveEnd Γ [o.formula A B] Θ).get (At.shift Γ (.here (o.formula A B) Θ))=
      At.shift (Γ++Θ) (.here (o.formula A B) []) := by
    simpa only [At.before,List.nil_append] using
      Route.moveEnd_middle Γ [o.formula A B] Θ (.here (o.formula A B) [])
  have ha : (Route.moveEnd Γ [A,B] Θ).get (At.shift Γ (.here A (B::Θ)))=
      At.shift (Γ++Θ) (.here A [B]) := by
    simpa only [At.before,List.singleton_append] using Route.moveEnd_middle Γ [A,B] Θ (.here A [B])
  have hb : (Route.moveEnd Γ [A,B] Θ).get (At.shift Γ (.there (.here B Θ)))=
      At.shift (Γ++Θ) (.there (.here B [])) := by
    simpa only [At.before,List.nil_append] using Route.moveEnd_middle Γ [A,B] Θ (.there (.here B []))
  apply side_ext o
  intro E a
  cases At.cases_append Γ ([A,B]++Θ) a with
  | inl h=>
    obtain ⟨a,rfl⟩:=h
    have hD:=Route.moveEnd_before Γ [o.formula A B] Θ a
    have hAB:=Route.moveEnd_before Γ [A,B] Θ a
    simp only [List.cons_append,List.nil_append] at hD hAB ⊢
    rw [(side P o).assoc,logical_prefix o Θ A B a,Route.sideArrow_get,hD,
      (side P o).assoc,Route.sideArrow_get,hAB,logical_prefix o [] A B (a.before Θ)]
  | inr h=>
    obtain ⟨a,rfl⟩:=h
    cases At.cases_append [A,B] Θ a with
    | inr h=>
      obtain ⟨a,rfl⟩:=h
      rw [(side P o).assoc,logical_tail,Route.sideArrow_get,Route.moveEnd_tail,
        (side P o).assoc,Route.sideArrow_get,Route.moveEnd_tail,logical_prefix]
    | inl h=>
      obtain ⟨a,rfl⟩:=h
      cases a with
      | here=>
        simp only [At.before,List.singleton_append]
        rw [(side P o).assoc,logical_first o Γ Θ A B,←(side P o).assoc,Route.sideArrow_get,hd,
          (side P o).assoc,Route.sideArrow_get,ha,logical_first o (Γ++Θ) [] A B]
      | there a=>
        cases a with
        | there a=>cases a
        | here=>
          simp only [At.before,List.nil_append]
          rw [(side P o).assoc,logical_second o Γ Θ A B,←(side P o).assoc,Route.sideArrow_get,hd,
            (side P o).assoc,Route.sideArrow_get,hb,logical_second o (Γ++Θ) [] A B]
end DosenPetric.Reduced.Gentzen
