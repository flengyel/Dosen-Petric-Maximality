module

public import DosenPetric.GentzenContextSelectionNormalization

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace ExchangeScript
variable {F U : List (NormalForm P)}

theorem inverse_arrow (p : ExchangeScript P F U) (o : Op) :
    (side P o).comp (p.inverse.arrow o) (p.arrow o)=(side P o).id _ := by
  apply side_ext o
  intro A a
  rw [(side P o).assoc,p.component,p.inverse.component,p.inverse_get,(side P o).id_comp]

theorem arrow_inverse (p : ExchangeScript P F U) (o : Op) :
    (side P o).comp (p.arrow o) (p.inverse.arrow o)=(side P o).id _ := by
  apply side_ext o
  intro A a
  rw [(side P o).assoc,p.inverse.component,p.component,p.get_inverse,(side P o).id_comp]
end ExchangeScript
namespace ContractionSelection
variable {C : NormalForm P} {Γ Θ K : List (NormalForm P)}

theorem normalizeContext_side (g : SelectionMask C Γ) (t : SelectionMask C Θ) (M : List (NormalForm P))
    (p : ContractionSelection C (Γ++(M++Θ)) K) (h : p.mask=SelectionMask.contextMask g t M) (o : Op) :
    (side P o).comp ((p.normalizeContext g t M h).arrow o) (p.route.sideArrow o)=
      (SelectionMask.contextCanonical g t M).sideArrow o := by
  apply side_ext o
  intro A a
  rw [(side P o).assoc,Route.sideArrow_get,ExchangeScript.component,Route.sideArrow_get]
  exact congrArg (component o)
    (by have he:=congrArg (fun r : Route (C::(g.erased++(M++t.erased))) (Γ++(M++Θ))=>r.get a)
          (p.normalizeContext_route g t M h)
        simpa only [Route.get_map] using he)
end ContractionSelection
end DosenPetric.Reduced.Gentzen
