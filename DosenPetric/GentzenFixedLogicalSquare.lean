module

public import DosenPetric.GentzenContextNormalizationLaws
public import DosenPetric.GentzenContextSelectionSums

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.FixedLogicalReducer
universe u
variable {P : Type u} {C : NormalForm P} {Γ Θ K L : List (NormalForm P)}
variable (g : SelectionMask C Γ) (t : SelectionMask C Θ) (o : Op) (A B : NormalForm P)
variable (q : ContractionSelection C (Γ++o.formula A B::Θ) K)
variable (p : ContractionSelection C (Γ++A::B::Θ) L)
variable (hq : q.mask=SelectionMask.contextMask g t [o.formula A B])
variable (hp : p.mask=SelectionMask.contextMask g t [A,B])

include hq hp in
theorem square :
    (side P o).comp (q.route.sideArrow o) (logicalSide o Γ Θ A B)=
      (side P o).comp ((q.normalizeContext g t [o.formula A B] hq).inverse.arrow o)
        ((side P o).comp (logicalSide o (C::g.erased) t.erased A B)
          ((side P o).comp ((p.normalizeContext g t [A,B] hp).arrow o) (p.route.sideArrow o))) := by
  let v:=q.normalizeContext g t [o.formula A B] hq
  let u:=p.normalizeContext g t [A,B] hp
  have h : (side P o).comp (v.arrow o)
      ((side P o).comp (q.route.sideArrow o) (logicalSide o Γ Θ A B))=
      (side P o).comp (logicalSide o (C::g.erased) t.erased A B)
        ((side P o).comp (u.arrow o) (p.route.sideArrow o)) := by
    rw [←(side P o).assoc,q.normalizeContext_side g t [o.formula A B] hq,
      SelectionMask.context_logical_square,←p.normalizeContext_side g t [A,B] hp]
  have he:=congrArg (fun f=>(side P o).comp (v.inverse.arrow o) f) h
  rw [←(side P o).assoc,v.inverse_arrow,(side P o).id_comp] at he
  exact he
end DosenPetric.Reduced.Gentzen.FixedLogicalReducer
