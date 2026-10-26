module

public import DosenPetric.GentzenSelectedOldRanks

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.SelectedLogicalReducer
universe u
variable {P : Type u} {C : NormalForm P} {Γ Θ K L : List (NormalForm P)}
variable (g : SelectionMask C Γ) (t : SelectionMask C Θ)
variable (q : ContractionSelection C (Γ++C::Θ) K) (p : ContractionSelection C (Γ++Θ) L)
variable (hq : q.mask=SelectionMask.selectedContext g t) (hp : p.mask=g.append t)

include hq hp in
theorem terminal_side (o : Op) :
    q.route.sideArrow o=(side P o).comp ((exit g t q p hq hp).arrow o)
      ((side P o).comp ((terminal p).route.sideArrow o) ((Route.moveEnd Γ [C] Θ).sideArrow o)) := by
  apply side_ext o
  intro A a
  rw [Route.sideArrow_get,(side P o).assoc,(side P o).assoc,
    Route.sideArrow_get,Route.sideArrow_get,ExchangeScript.component]
  exact congrArg (component o) (exit_square g t q p hq hp a)

theorem source_keep_index (o : Op) (A B : NormalForm P)
    {F K : List (NormalForm P)} (p : ContractionSelection (o.formula A B) F K) :
    (terminal p).keep.index=(p.logicalData o A B).x.index := by
  have h0 : (terminal p).keep.index=p.erased.length := by
    rw [terminal,p.chain_keep,At.index_shift]
    rfl
  have h1 : (p.logicalData o A B).x.index=(gaps p.gs).length+p.tail.length :=
    (p.logicalData o A B).s.x_index
  have h2 : p.erased.length=(gaps p.gs).length+p.tail.length :=
    (congrArg List.length p.erased_eq).trans List.length_append
  exact h0.trans (h2.trans h1.symm)
end SelectedLogicalReducer
namespace SelectedLogicalReducer
universe u
variable {P : Type u} {Γ Θ K L : List (NormalForm P)}
variable (o : Op) (A B : NormalForm P)
variable (g : SelectionMask (o.formula A B) Γ) (t : SelectionMask (o.formula A B) Θ)
variable (q : ContractionSelection (o.formula A B) (Γ++o.formula A B::Θ) K)
variable (p : ContractionSelection (o.formula A B) (Γ++Θ) L)
variable (hq : q.mask=SelectionMask.selectedContext g t) (hp : p.mask=g.append t)

include hq hp in
theorem logical_terminal_side :
    (side P o).comp (q.route.sideArrow o) (logicalSide o Γ Θ A B)=
      (side P o).comp ((exit g t q p hq hp).arrow o)
        ((side P o).comp ((terminal p).route.sideArrow o)
          ((side P o).comp (logicalSide o (Γ++Θ) [] A B) ((Route.moveEnd Γ [A,B] Θ).sideArrow o))) := by
  rw [terminal_side g t q p hq hp o,(side P o).assoc,(side P o).assoc,logical_terminal_square]
end SelectedLogicalReducer
end DosenPetric.Reduced.Gentzen
