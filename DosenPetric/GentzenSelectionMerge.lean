module

public import DosenPetric.GentzenSelectionContraction

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.ContractionSelection
universe u
variable {P : Type u} {C : NormalForm P}
variable {F K U L : List (NormalForm P)}

/-- Merge the two retained copies after the independent contractions. -/
def mergeRoute {F K U L : List (NormalForm P)}
    (p : ContractionSelection C F K) (q : ContractionSelection C U L) :
    Route (p.erased++L) (K++L) :=
  match p with
  | .last Θ => .cons (At.shift Θ q.keep) (Route.identity (Θ++L))
  | .fixed A p => .cons (.here A _) ((mergeRoute p q).map At.there)
  | .more p => mergeRoute p q

theorem merge_keep (p : ContractionSelection C F K) (q : ContractionSelection C U L) :
    (p.mergeRoute q).get (p.keep.before L) = At.shift p.erased q.keep := by
  induction p with
  | last => rfl
  | fixed A p ih => simpa only [mergeRoute,keep,At.before,Route.get,Route.get_map,erased,At.shift] using congrArg At.there ih
  | more p ih => exact ih

theorem merge_shift (p : ContractionSelection C F K) (q : ContractionSelection C U L)
    {A : NormalForm P} (a : At L A) :
    (p.mergeRoute q).get (At.shift K a) = At.shift p.erased a := by
  induction p with
  | last Θ => exact Route.get_identity _
  | fixed A p ih => simpa only [mergeRoute,At.shift,Route.get,Route.get_map,erased] using congrArg At.there ih
  | more p ih => exact ih

theorem chain_before (p : ContractionSelection C F K) (q : ContractionSelection C U L)
    {A : NormalForm P} (a : At F A) :
    (p.chain q).route.get (a.before U) =
      (p.mergeRoute q).get ((p.route.get a).before L) := by
  induction p with
  | last Θ =>
    cases a with
    | here => exact chain_keep (.last Θ) q
    | there a =>
      dsimp only [chain,route,mergeRoute,Route.get,At.before]
      rw [Route.get_identity]
      change (q.prependFixed Θ).route.get (a.before U) =
        (Route.identity (Θ++L)).get (a.before L)
      rw [prepend_before,Route.get_identity]
  | fixed B p ih =>
    cases a with
    | here => rfl
    | there a =>
      dsimp only [chain,route,mergeRoute,At.before]
      simpa only [Route.get,Route.get_map,At.before] using congrArg At.there (ih a)
  | more p ih =>
    cases a with
    | here => exact (chain_keep p q).trans (merge_keep p q).symm
    | there a => exact ih a

theorem merge_index (p : ContractionSelection C F K) (q : ContractionSelection C U L)
    {A : NormalForm P} (a : At (K++L) A) :
    ((p.mergeRoute q).get a).index =
      copyIndex [gaps p.gs,p.tail++gaps q.gs] a.index := by
  induction p with
  | last Θ =>
    cases a with
    | here =>
      change (At.shift Θ q.keep).index = copyIndex [[],Θ++gaps q.gs] 0
      rw [At.index_shift,q.keep_index]
      simp only [copyIndex,gaps,List.length_nil,Nat.lt_irrefl,ite_false,ite_true,
        Nat.zero_add,List.append_nil,List.length_append]
    | there a =>
      change ((Route.identity (Θ++L)).get a).index = copyIndex [[],Θ++gaps q.gs] (a.index+1)
      rw [Route.get_identity]
      simp only [copyIndex,gaps,List.length_nil,Nat.not_lt_zero,ite_false,Nat.zero_add]
      repeat first | split | omega
  | fixed B p ih =>
    cases a with
    | here =>
      change 0 = copyIndex [(A::gaps p.gs),p.tail++gaps q.gs] 0
      simp only [copyIndex,List.length_cons,Nat.zero_lt_succ,ite_true]
    | there a =>
      dsimp only [mergeRoute]
      simp only [Route.get,Route.get_map]
      change ((p.mergeRoute q).get a).index+1 =
        copyIndex [(B::gaps p.gs),p.tail++gaps q.gs] (a.index+1)
      rw [copyIndex_front,ih]
  | more p ih =>
    change ((p.mergeRoute q).get a).index = copyIndex [gaps p.gs,p.tail++gaps q.gs] a.index
    exact ih a

abbrev mergeBlock (p : ContractionSelection C F K) (q : ContractionSelection C U L) :
    ContractionBlock P (K++L) (p.erased++L) where
  C := C
  gs := [gaps p.gs,p.tail++gaps q.gs]
  tail := q.tail
  upper := by
    calc
      _ = (gaps p.gs++C::p.tail)++(gaps q.gs++C::q.tail) := by
        simp only [repeated,List.nil_append,List.append_assoc,List.cons_append]
      _ = K++L := by simp only [p.lower,q.lower]
  lower := by
    calc
      _ = (gaps p.gs++p.tail)++(gaps q.gs++C::q.tail) := by
        simp only [gaps,List.append_nil,List.append_assoc]
      _ = p.erased++L := by simp only [p.erased_eq,q.lower]

theorem merge_route (p : ContractionSelection C F K) (q : ContractionSelection C U L) :
    p.mergeRoute q = (p.mergeBlock q).route := by
  apply Route.ext_get
  intro A a
  apply At.index_injective
  rw [merge_index,ContractionBlock.get_index]

theorem merge_retained (p : ContractionSelection C F K) (q : ContractionSelection C U L) :
    (p.mergeBlock q).keep = (p.chain q).keep := by
  rw [chain_keep]
  apply At.index_injective
  simp only [ContractionBlock.keep_index,mergeBlock,gaps,List.append_nil,List.length_append,
    At.index_shift,q.keep_index,p.erased_eq]
  omega

theorem merge_selected (p : ContractionSelection C F K) (q : ContractionSelection C U L) :
    (p.mergeBlock q).selected = [p.keep.before L,At.shift K q.keep] := by
  apply At.list_index_injective
  rw [ContractionBlock.selected_indices]
  change [ (gaps p.gs).length,
    (gaps p.gs).length+1+(p.tail++gaps q.gs).length ] = _
  simp only [List.map_cons,List.map_nil,At.index_before,At.index_shift,p.keep_index,q.keep_index,
    List.length_append]
  have hl : K.length = (gaps p.gs).length+(p.tail.length+1) := by
    simpa only [List.length_append,List.length_cons] using (congrArg List.length p.lower).symm
  simp only [gaps,List.length_append] at hl
  apply congrArg (fun i : Nat => [p.first.length+(gaps p.rest).length,i])
  omega

end DosenPetric.Reduced.Gentzen.ContractionSelection
