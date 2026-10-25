module

public import DosenPetric.GentzenRetainedSelection

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.ContractionSelection
universe u
variable {P : Type u} {C : NormalForm P}
variable {F K U L V J : List (NormalForm P)}

theorem selected_indices (p : ContractionSelection C F K) :
    p.selected.map At.index=copyOffsets p.gs :=
  (congrArg (List.map At.index) p.selected_eq).trans p.block.selected_indices

theorem eq_of_gs (p q : ContractionSelection C F K) (hg : p.gs=q.gs) : p=q := by
  apply ext_selected
  apply At.list_index_injective
  rw [selected_indices,selected_indices,hg]

theorem arity_cast {F' K' : List (NormalForm P)} (p : ContractionSelection C F K)
    (hF : F=F') (hK : K=K') : (p.cast hF hK).arity=p.arity :=
  (p.cast hF hK).count.symm.trans ((congrArg List.length (gs_cast hF hK p)).trans p.count)
theorem selected_cast {F' K' : List (NormalForm P)} (p : ContractionSelection C F K)
    (hF : F=F') (hK : K=K') : (p.cast hF hK).selected=p.selected.map (At.cast hF) := by
  cases hF; cases hK; exact (List.map_id _).symm
theorem keep_cast {F' K' : List (NormalForm P)} (p : ContractionSelection C F K)
    (hF : F=F') (hK : K=K') : (p.cast hF hK).keep=p.keep.cast hK := by
  cases hF; cases hK; rfl

theorem prepend_erased (p : ContractionSelection C F K) (Ξ : List (NormalForm P)) :
    (p.prependFixed Ξ).erased=Ξ++p.erased := by
  induction Ξ with
  | nil => rfl
  | cons A Ξ ih => exact congrArg (List.cons A) ih

theorem erased_chain (p : ContractionSelection C F K) (q : ContractionSelection C U L) :
    (p.chain q).erased=p.erased++q.erased := by
  induction p with
  | last Θ => exact q.prepend_erased Θ
  | fixed A p ih => exact congrArg (List.cons A) ih
  | more p ih => exact ih
theorem chain_first (p : ContractionSelection C F K) (q : ContractionSelection C U L) :
    (p.chain q).first=p.first := by
  induction p with
  | last => rfl
  | fixed A p ih => exact congrArg (List.cons A) ih
  | more => rfl
theorem chain_rest (p : ContractionSelection C F K) (q : ContractionSelection C U L) :
    (p.chain q).rest=p.rest++(p.tail++q.first)::q.rest := by
  induction p with
  | last Θ =>
    change (q.prependFixed Θ).first::(q.prependFixed Θ).rest = _
    rw [first_prependFixed,rest_prependFixed]
    rfl
  | fixed A p ih => exact ih
  | more p ih =>
    change (p.chain q).first::(p.chain q).rest = _
    rw [chain_first,ih]
    rfl
theorem chain_tail (p : ContractionSelection C F K) (q : ContractionSelection C U L) :
    (p.chain q).tail=q.tail := by
  induction p with
  | last Θ => exact tail_prependFixed Θ q
  | fixed A p ih => exact ih
  | more p ih => exact ih
theorem chain_gs (p : ContractionSelection C F K) (q : ContractionSelection C U L) :
    (p.chain q).gs=p.gs++(p.tail++q.first)::q.rest := by
  change (p.chain q).first::(p.chain q).rest = _
  rw [chain_first,chain_rest]
  rfl

theorem chain_lower_assoc (p : ContractionSelection C F K) (q : ContractionSelection C U L)
    (J : List (NormalForm P)) : (p.chain q).erased++J=p.erased++(q.erased++J) :=
  (congrArg (fun Ξ => Ξ++J) (p.erased_chain q)).trans (List.append_assoc _ _ _)

theorem chain_assoc (p : ContractionSelection C F K) (q : ContractionSelection C U L)
    (r : ContractionSelection C V J) :
    ((p.chain q).chain r).cast (List.append_assoc F U V) (p.chain_lower_assoc q J) =
      p.chain (q.chain r) := by
  apply eq_of_gs
  rw [gs_cast,chain_gs,chain_gs,chain_tail,chain_gs,chain_first,chain_rest]
  simp only [List.append_assoc,List.cons_append]

theorem retain_first (p : ContractionSelection C F K) (q : ContractionSelection C U L) :
    (p.retainChain q).first=gaps p.gs := by
  induction p with
  | last => rfl
  | fixed A p ih => simpa only [retainChain,first,gs,rest,gaps,List.cons_append] using congrArg (List.cons A) ih
  | more p ih => simpa only [retainChain,gs,first,rest,gaps,List.nil_append] using ih
theorem retain_rest (p : ContractionSelection C F K) (q : ContractionSelection C U L) :
    (p.retainChain q).rest=(p.tail++q.first)::q.rest := by
  induction p with
  | last Θ =>
    change (q.prependFixed Θ).first::(q.prependFixed Θ).rest = _
    rw [first_prependFixed,rest_prependFixed]
    rfl
  | fixed A p ih => exact ih
  | more p ih => exact ih
theorem retain_tail (p : ContractionSelection C F K) (q : ContractionSelection C U L) :
    (p.retainChain q).tail=q.tail := by
  induction p with
  | last Θ => exact tail_prependFixed Θ q
  | fixed A p ih => exact ih
  | more p ih => exact ih

theorem retained_factor (p : ContractionSelection C F K) (q : ContractionSelection C U L)
    (r : ContractionSelection C V J) (o : Op) :
    (p.chain (q.chain r)).route.sideArrow o =
      (side P o).comp ((p.retainChain (q.retainChain r)).route.sideArrow o)
        ((side P o).comp (((q.extend V).prependFixed K).route.sideArrow o)
          ((p.extend (U++V)).route.sideArrow o)) := by
  rw [←fuse_extend p (q.chain r),fuse_side,←retain_fuse p q r,fuse_side,(side P o).assoc]

end DosenPetric.Reduced.Gentzen.ContractionSelection
