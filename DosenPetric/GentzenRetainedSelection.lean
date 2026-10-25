module

public import DosenPetric.GentzenSelectionExtension

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.ContractionSelection
universe u
variable {P : Type u} {C : NormalForm P}

/-- Select the retained copy of p and all copies selected by q. -/
def retainChain {F K U L : List (NormalForm P)} (p : ContractionSelection C F K)
    (q : ContractionSelection C U L) : ContractionSelection C (K++U) (p.erased++L) :=
  match p with
  | .last Θ => .more (q.prependFixed Θ)
  | .fixed A p => .fixed A (p.retainChain q)
  | .more p => p.retainChain q

variable {F K U L V J : List (NormalForm P)}

theorem retain_selected (p : ContractionSelection C F K) (q : ContractionSelection C U L) :
    (p.retainChain q).selected = p.keep.before U :: q.selected.map (At.shift K) := by
  induction p with
  | last Θ =>
    change .here C _::(q.prependFixed Θ).selected.map At.there = _
    rw [prepend_selected]
    simp only [List.map_map]
    rfl
  | fixed A p ih =>
    simp only [retainChain,selected,ih,List.map_cons,List.map_map]
    rfl
  | more p ih => exact ih

theorem retain_member (p : ContractionSelection C F K) (q : ContractionSelection C U L) :
    (p.extend U).keep ∈ (p.retainChain q).selected := by
  rw [extend_keep,retain_selected]
  exact List.mem_cons_self

theorem fuse_extend (p : ContractionSelection C F K) (q : ContractionSelection C U L) :
    (p.extend U).fuse (p.retainChain q) (p.retain_member q) = p.chain q := by
  induction p with
  | last => rfl
  | fixed A p ih => exact congrArg (fixed A) ih
  | more p ih => exact congrArg more ih

theorem prepend_member {I : List (NormalForm P)} (p : ContractionSelection C F I)
    (q : ContractionSelection C I K) (h : p.keep ∈ q.selected) (Ξ : List (NormalForm P)) :
    (p.prependFixed Ξ).keep ∈ (q.prependFixed Ξ).selected := by
  rw [prepend_keep,prepend_selected]
  exact List.mem_map_of_mem h

theorem fuse_prepend {I : List (NormalForm P)} (p : ContractionSelection C F I)
    (q : ContractionSelection C I K) (h : p.keep ∈ q.selected) (Ξ : List (NormalForm P)) :
    (p.prependFixed Ξ).fuse (q.prependFixed Ξ) (prepend_member p q h Ξ) =
      (p.fuse q h).prependFixed Ξ := by
  induction Ξ with
  | nil => rfl
  | cons A Ξ ih => exact congrArg (fixed A) ih

theorem retain_fuse_member (p : ContractionSelection C F K) (q : ContractionSelection C U L)
    (r : ContractionSelection C V J) :
    ((q.extend V).prependFixed K).keep ∈ (p.retainChain (q.retainChain r)).selected := by
  rw [prepend_keep,extend_keep,retain_selected,retain_selected]
  apply List.mem_cons_of_mem
  exact List.mem_map_of_mem List.mem_cons_self

theorem retain_fuse (p : ContractionSelection C F K) (q : ContractionSelection C U L)
    (r : ContractionSelection C V J) :
    ((q.extend V).prependFixed K).fuse (p.retainChain (q.retainChain r))
      (p.retain_fuse_member q r) = p.retainChain (q.chain r) := by
  induction p with
  | last Θ =>
    change more (((q.extend V).prependFixed Θ).fuse ((q.retainChain r).prependFixed Θ)
      (prepend_member (q.extend V) (q.retainChain r) (q.retain_member r) Θ)) =
      more ((q.chain r).prependFixed Θ)
    exact congrArg more ((fuse_prepend (q.extend V) (q.retainChain r)
      (q.retain_member r) Θ).trans (congrArg (fun s => s.prependFixed Θ) (q.fuse_extend r)))
  | fixed A p ih => exact congrArg (fixed A) ih
  | more p ih => exact ih

theorem fuse_side {I : List (NormalForm P)} (p : ContractionSelection C F I)
    (q : ContractionSelection C I K) (h : p.keep ∈ q.selected) (o : Op) :
    (p.fuse q h).route.sideArrow o =
      (side P o).comp (q.route.sideArrow o) (p.route.sideArrow o) := by
  apply side_ext o
  intro A a
  rw [(side P o).assoc,Route.sideArrow_get,Route.sideArrow_get,Route.sideArrow_get,fuse_get]

end DosenPetric.Reduced.Gentzen.ContractionSelection
