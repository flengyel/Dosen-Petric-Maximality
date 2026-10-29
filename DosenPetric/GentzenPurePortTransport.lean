module

public import DosenPetric.GentzenPurePortCoordinates

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.PurePort
universe u
variable {P : Type u}

theorem context_cases {o : Op} {Γ : List (NormalForm P)} {l : Literal P}
    (p : PurePort o (fold o Γ) l) :
    ∃ (A : NormalForm P) (a : At Γ A) (q : PurePort o A l), p = inContext o a q := by
  induction Γ with
  | nil => cases o <;> cases p
  | cons A Γ ih =>
    cases o <;> (cases p with
      | left B q => exact ⟨A,.here A Γ,q,rfl⟩
      | right A p =>
        obtain ⟨B,a,q,rfl⟩ := ih p
        exact ⟨B,a.there,q,rfl⟩)

/-- A structural route maps every literal path to its exact original port. -/
theorem route_factor (o : Op) {F U : List (NormalForm P)} (r : Route F U)
    {l : Literal P} (p : PurePort o (fold o U) l) :
    ∃ q : PurePort o (fold o F) l,
      (side P o).comp (r.sideArrow o) p.arrow = q.arrow := by
  obtain ⟨A,a,p,rfl⟩ := context_cases p
  refine ⟨inContext o (r.get a) p,?_⟩
  rw [inContext_arrow,inContext_arrow,← (side P o).assoc,Route.sideArrow_get]

/-- Unary logical reassociation maps both consumed components and every fixed
context port, retaining the left/right tags even when labels coincide. -/
theorem logical_factor (o : Op) (F U : List (NormalForm P)) (A B : NormalForm P)
    {l : Literal P} (p : PurePort o (fold o (F ++ A :: B :: U)) l) :
    ∃ q : PurePort o (fold o (F ++ o.formula A B :: U)) l,
      (side P o).comp (logicalSide o F U A B) p.arrow = q.arrow := by
  obtain ⟨C,a,p,rfl⟩ := context_cases p
  cases At.cases_append F (A :: B :: U) a with
  | inl ha =>
    obtain ⟨a,rfl⟩ := ha
    refine ⟨inContext o (a.before (o.formula A B :: U)) p,?_⟩
    rw [inContext_arrow,inContext_arrow,← (side P o).assoc,logical_prefix]
  | inr ha =>
    obtain ⟨a,rfl⟩ := ha
    cases a with
    | here =>
      refine ⟨inContext o (At.shift F (.here (o.formula A B) U)) (.left B p),?_⟩
      rw [inContext_arrow,inContext_arrow,← (side P o).assoc,logical_first,arrow,
        (side P o).assoc]
    | there a =>
      cases a with
      | here =>
        refine ⟨inContext o (At.shift F (.here (o.formula A B) U)) (.right A p),?_⟩
        rw [inContext_arrow,inContext_arrow,← (side P o).assoc,logical_second,arrow,
          (side P o).assoc]
      | there a =>
        refine ⟨inContext o (At.shift F (At.shift [o.formula A B] a)) p,?_⟩
        change (side P o).comp (logicalSide o F U A B)
          (inContext o (At.shift F (At.shift [A,B] a)) p).arrow = _
        rw [inContext_arrow,inContext_arrow,← (side P o).assoc,logical_tail]

end DosenPetric.Reduced.Gentzen.PurePort
