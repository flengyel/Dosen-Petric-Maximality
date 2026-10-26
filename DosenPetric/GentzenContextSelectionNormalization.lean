module

public import DosenPetric.GentzenMaskContextSelections
public import DosenPetric.GentzenExchangeFactor

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.ContractionSelection
universe u
variable {P : Type u} {C : NormalForm P} {Γ Θ K : List (NormalForm P)}

def normalizeContext (g : SelectionMask C Γ) (t : SelectionMask C Θ) (M : List (NormalForm P))
    (p : ContractionSelection C (Γ++(M++Θ)) K) (h : p.mask=SelectionMask.contextMask g t M) :
    ExchangeScript P (C::(g.erased++(M++t.erased))) K :=
  (p.normalizeAs _ h).reindex
    (congrArg (List.cons C) (SelectionMask.context_erased g t M)) rfl

theorem normalizeContext_route (g : SelectionMask C Γ) (t : SelectionMask C Θ) (M : List (NormalForm P))
    (p : ContractionSelection C (Γ++(M++Θ)) K) (h : p.mask=SelectionMask.contextMask g t M) :
    p.route.map (p.normalizeContext g t M h).get=SelectionMask.contextCanonical g t M := by
  apply Route.ext_get
  intro A a
  rw [Route.get_map]
  apply At.index_injective
  change (((p.normalizeAs _ h).get (p.route.get a)).cast _).index=_
  rw [At.index_cast,p.normalizeAs_index,SelectionMask.contextCanonical_index,SelectionMask.canonical_index]

theorem normalizeContext_keep (g : SelectionMask C Γ) (t : SelectionMask C Θ) (M : List (NormalForm P))
    (p : ContractionSelection C (Γ++(M++Θ)) K) (h : p.mask=SelectionMask.contextMask g t M) :
    (p.normalizeContext g t M h).get p.keep=.here C _ := by
  apply At.index_injective
  change (((p.normalizeAs _ h).get p.keep).cast _).index=0
  rw [At.index_cast,p.normalizeAs_keep]
  rfl
end DosenPetric.Reduced.Gentzen.ContractionSelection
