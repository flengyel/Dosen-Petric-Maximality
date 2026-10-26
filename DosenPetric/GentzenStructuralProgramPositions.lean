module

public import DosenPetric.GentzenStructuralPrograms

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.StructuralProgram
universe u
variable {P : Type u} {F U : List (NormalForm P)}

theorem consFixed_here (A : NormalForm P) (p : StructuralProgram P F U) :
    (p.consFixed A).get (.here A U)=.here A F := by
  induction p with
  | identity=>rfl
  | seq p q ih ih'=>exact (congrArg (p.consFixed A).get ih').trans ih
  | exchange Γ X Y Θ=>
    apply At.index_injective
    change (At.swapBlocks (A::Γ) X Y Θ (.here A _)).index=0
    rw [swapBlocks_index]
    simp only [At.index,List.length_cons,exchangeIndex]
    exact ite_eq_left (by omega)
  | thin Γ Θ B=>
    apply At.index_injective
    change ((Route.thin (A::Γ) Θ B).get (.here A _)).index=0
    rfl
  | contract C gs Θ hn=>
    cases gs with
    | nil=>change 2≤0 at hn;omega
    | cons H hs=>
      apply At.index_injective
      change ((copies C ((A::H)::hs) Θ).get (.here A _)).index=0
      rw [copies_index]
      simp only [copyIndex,At.index,List.length_cons]
      exact ite_eq_left (by omega)
  | reindex hF hU p ih=>cases hF;cases hU;exact ih

theorem consFixed_there (A : NormalForm P) (p : StructuralProgram P F U)
    {B : NormalForm P} (a : At U B) :
    (p.consFixed A).get a.there=(p.get a).there := by
  induction p with
  | identity=>rfl
  | seq p q ih ih'=>exact (congrArg (p.consFixed A).get (ih' a)).trans (ih (q.get a))
  | exchange Γ X Y Θ=>
    apply At.index_injective
    change (At.swapBlocks (A::Γ) X Y Θ a.there).index=(At.swapBlocks Γ X Y Θ a).index+1
    rw [swapBlocks_index,swapBlocks_index]
    simp only [List.length_cons,At.index,Nat.add_comm]
    unfold exchangeIndex
    split <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> omega
  | thin Γ Θ D=>
    change ((Route.thin Γ Θ D).map (fun x=>x.there)).get a=((Route.thin Γ Θ D).get a).there
    exact Route.get_map ..
  | contract C gs Θ hn=>
    cases gs with
    | nil=>change 2≤0 at hn;omega
    | cons H hs=>
      apply At.index_injective
      change ((copies C ((A::H)::hs) Θ).get a.there).index=((copies C (H::hs) Θ).get a).index+1
      rw [copies_index,copies_index]
      change copyIndex ((A::H)::hs) (a.index+1)=copyIndex (H::hs) a.index+1
      exact ContractionSelection.copyIndex_front A H hs a.index
  | reindex hF hU p ih=>cases hF;cases hU;exact ih a
end DosenPetric.Reduced.Gentzen.StructuralProgram
