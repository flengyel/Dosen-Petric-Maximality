module

public import DosenPetric.GentzenLogicalRetainedFactor
public import DosenPetric.GentzenHeadRoutes

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace ContractionSelection
variable {C : NormalForm P}

def retained : {F K : List (NormalForm P)}→ContractionSelection C F K→ContractionSelection C K K
  | _,_,.last Θ => .last Θ
  | _,_,.fixed A p => .fixed A p.retained
  | _,_,.more p => p.retained

variable {F K : List (NormalForm P)} (p : ContractionSelection C F K)
theorem retained_arity : p.retained.arity=1 := by induction p <;> simp_all only [retained,arity]
theorem retained_keep : p.retained.keep=p.keep := by
  induction p with
  | last => rfl
  | fixed A p ih => exact congrArg At.there ih
  | more p ih => exact ih
theorem retained_tail : p.retained.tail=p.tail := by induction p <;> simp_all only [retained,tail]
theorem retained_first : p.retained.first=gaps p.gs := by
  induction p with
  | last => rfl
  | fixed A p ih => simpa only [retained,first,gs,rest,gaps,List.cons_append] using congrArg (List.cons A) ih
  | more p ih => simpa only [retained,gs,first,rest,gaps,List.nil_append] using ih
theorem retained_rest : p.retained.rest=[] := by induction p <;> simp_all only [retained,rest]
theorem retained_gs : p.retained.gs=[gaps p.gs] := by change p.retained.first::p.retained.rest=_; rw [retained_first,retained_rest]
theorem retained_route : p.retained.route=Route.identity K := by
  apply Route.ext_get
  intro A a
  rw [p.retained.singleton_get p.retained_arity,Route.get_identity]
  rfl
end ContractionSelection

namespace ContractionBlock
variable {F K : List (NormalForm P)} (d : ContractionBlock P F K) (hn : 2≤d.gs.length)

theorem prepend_head_route (D : NormalForm P) :
    (d.prepend hn [D]).route=d.route.head D := by
  apply Route.ext_get
  intro A a
  cases a with
  | here => exact d.prepend_before hn [D] (.here D [])
  | there a => simpa only [Route.head,Route.get,Route.get_map,At.shift] using d.prepend_shift hn [D] a

end ContractionBlock
end DosenPetric.Reduced.Gentzen
