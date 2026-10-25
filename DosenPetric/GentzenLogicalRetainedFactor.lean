module

public import DosenPetric.GentzenSelectionRouteExtension
public import DosenPetric.GentzenSelectionSplit
public import DosenPetric.GentzenTerminalLogicalNaturality

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u} {C : NormalForm P} {F K U L : List (NormalForm P)}
namespace Route

theorem cast_inverse {F K F' K' : List (NormalForm P)} (p : Route K F)
    (hK : K=K') (hF : F=F') : (p.cast hK hF).cast hK.symm hF.symm=p := by
  cases hK; cases hF; rfl

theorem parallel_assoc_reverse {F K U L V J : List (NormalForm P)}
    (p : Route K F) (q : Route L U) (r : Route J V) :
    (p.parallel (q.parallel r)).cast (List.append_assoc K L J).symm (List.append_assoc F U V).symm =
      (p.parallel q).parallel r := by
  have h:=congrArg (fun w : Route (K++(L++J)) (F++(U++V)) =>
    w.cast (List.append_assoc K L J).symm (List.append_assoc F U V).symm) (parallel_assoc p q r)
  rw [cast_inverse] at h
  exact h.symm
end Route
namespace ContractionSelection

theorem cast_trans {F K F' K' F'' K'' : List (NormalForm P)}
    (p : ContractionSelection C F K) (hF : F=F') (hK : K=K')
    (jF : F'=F'') (jK : K'=K'') :
    (p.cast hF hK).cast jF jK=p.cast (hF.trans jF) (hK.trans jK) := by
  cases hF; cases hK; cases jF; cases jK; rfl

theorem cast_refl {F K : List (NormalForm P)} (p : ContractionSelection C F K) :
    p.cast rfl rfl=p := rfl

theorem retained_middle {V : List (NormalForm P)} (p : ContractionSelection C F K)
    (q : ContractionSelection C U L) :
    ((q.extend V).prependFixed K).route.compose (p.extend (U++V)).route =
      p.route.parallel (q.route.parallel (Route.identity V)) := by
  rw [←q.extend_route V]
  apply Route.ext_get
  intro A a
  rw [Route.compose_get]
  cases At.cases_append F (U++V) a with
  | inl h =>
    obtain ⟨a,rfl⟩:=h
    rw [extend_before,prepend_before,Route.parallel_before]
  | inr h =>
    obtain ⟨a,rfl⟩:=h
    rw [extend_shift,prepend_shift,Route.parallel_shift]

def sourceOld (p : ContractionSelection C F K) (q : ContractionSelection C U L) :
    ContractionSelection C ((F++U)++[C]) (p.erased++(q.erased++[C])) :=
  (p.chain (q.chain (.last []))).cast (List.append_assoc F U [C]).symm rfl

def sourceRetained (p : ContractionSelection C F K) (q : ContractionSelection C U L) :
    ContractionSelection C ((K++L)++[C]) (p.erased++(q.erased++[C])) :=
  (p.retainChain (q.retainChain (.last []))).cast (List.append_assoc K L [C]).symm rfl

theorem sourceOld_assoc (p : ContractionSelection C F K) (q : ContractionSelection C U L) :
    (p.sourceOld q).cast rfl (p.chain_lower_assoc q [C]).symm=(p.chain q).chain (.last []) := by
  have h:=p.chain_assoc q (.last [])
  have hc:=congrArg (fun s : ContractionSelection C (F++(U++[C])) (p.erased++(q.erased++[C])) =>
    s.cast (List.append_assoc F U [C]).symm (p.chain_lower_assoc q [C]).symm) h
  simpa only [sourceOld,cast_trans,cast_refl] using hc.symm

theorem source_factor (p : ContractionSelection C F K) (q : ContractionSelection C U L) (o : Op) :
    (p.sourceOld q).route.sideArrow o=(side P o).comp ((p.sourceRetained q).route.sideArrow o)
      (((p.route.parallel q.route).parallel (Route.identity [C])).sideArrow o) := by
  have h:=p.retained_factor q (.last []) o
  rw [←Route.compose_side,retained_middle] at h
  have hc:=Route.cast_factor _ _ _ o h (List.append_assoc F U [C]).symm (List.append_assoc K L [C]).symm
  simpa only [sourceOld,sourceRetained,route_cast,Route.parallel_assoc_reverse] using hc

theorem retain_arity (p : ContractionSelection C F K) (q : ContractionSelection C U L) :
    (p.retainChain q).arity=q.arity+1 := by
  induction p with
  | last Θ => change (q.prependFixed Θ).arity+1=q.arity+1; rw [prepend_arity]
  | fixed A p ih => exact ih
  | more p ih => exact ih

theorem sourceRetained_arity (p : ContractionSelection C F K) (q : ContractionSelection C U L) :
    (p.sourceRetained q).arity=3 := by rw [sourceRetained,arity_cast,retain_arity,retain_arity]; rfl

theorem sourceOld_arity (p : ContractionSelection C F K) (q : ContractionSelection C U L) :
    (p.sourceOld q).arity=p.arity+q.arity+1 := by
  rw [sourceOld,arity_cast,chain_count,chain_count]
  change p.arity+(q.arity+1)=p.arity+q.arity+1
  omega

end ContractionSelection
end DosenPetric.Reduced.Gentzen
