module

public import DosenPetric.GentzenSelectionContraction

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.ContractionSelection
universe u
variable {P : Type u} {C : NormalForm P}

def extend {F K : List (NormalForm P)} (p : ContractionSelection C F K)
    (Ξ : List (NormalForm P)) : ContractionSelection C (F++Ξ) (K++Ξ) :=
  match p with
  | .last Θ => .last (Θ++Ξ)
  | .fixed A p => .fixed A (p.extend Ξ)
  | .more p => .more (p.extend Ξ)

variable {F K : List (NormalForm P)} (p : ContractionSelection C F K)
theorem extend_first (Ξ : List (NormalForm P)) : (p.extend Ξ).first=p.first := by
  induction p <;> simp_all only [extend,first]
theorem extend_rest (Ξ : List (NormalForm P)) : (p.extend Ξ).rest=p.rest := by
  induction p <;> simp_all only [extend,rest,extend_first]
theorem extend_tail (Ξ : List (NormalForm P)) : (p.extend Ξ).tail=p.tail++Ξ := by
  induction p <;> simp_all only [extend,tail]
theorem extend_arity (Ξ : List (NormalForm P)) : (p.extend Ξ).arity=p.arity := by
  induction p <;> simp_all only [extend,arity]
theorem extend_gs (Ξ : List (NormalForm P)) : (p.extend Ξ).gs=p.gs := by
  change (p.extend Ξ).first::(p.extend Ξ).rest = p.first::p.rest
  rw [extend_first,extend_rest]
theorem extend_block (Ξ : List (NormalForm P)) : (p.extend Ξ).block=p.block.extend Ξ := by
  exact block_match (p.extend Ξ) (p.block.extend Ξ) rfl (p.extend_gs Ξ) (p.extend_tail Ξ)
theorem extend_keep (Ξ : List (NormalForm P)) : (p.extend Ξ).keep=p.keep.before Ξ := by
  induction p with
  | last => rfl
  | fixed A p ih => exact congrArg At.there ih
  | more p ih => exact ih
theorem extend_selected (Ξ : List (NormalForm P)) :
    (p.extend Ξ).selected=p.selected.map (fun a => a.before Ξ) := by
  induction p with
  | last => rfl
  | fixed A p ih =>
    simp only [extend,selected,ih,List.map_map]
    rfl
  | more p ih =>
    change .here C _::(p.extend Ξ).selected.map At.there = _
    rw [ih]
    simp only [selected,List.map_cons,List.map_map]
    rfl
theorem extend_erased (Ξ : List (NormalForm P)) : (p.extend Ξ).erased=p.erased++Ξ := by
  rw [erased_eq,extend_gs,extend_tail,p.erased_eq,List.append_assoc]
  simp only [gaps,List.append_assoc]

end DosenPetric.Reduced.Gentzen.ContractionSelection
