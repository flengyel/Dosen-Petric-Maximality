module

public import DosenPetric.GentzenBlockedDisjSecondRank

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace At

theorem retain_injective {F : List (NormalForm P)} {C E : NormalForm P}
    (x : At F C) (a b : At x.erase E) (h : x.retain a = x.retain b) : a = b := by
  induction x with
  | here => exact At.there.inj h
  | there x ih =>
    cases a with
    | here => cases b with
      | here => rfl
      | there b => cases h
    | there a => cases b with
      | here => cases h
      | there b => exact congrArg At.there (ih a b (At.there.inj h))

end At
namespace Route

theorem singleFiber_compose {F U V : List (NormalForm P)} {C : NormalForm P}
    (r : Route F U) (s : Route U V) (x : At F C) (y : At U C) (z : At V C)
    (hr : r.SingleFiber x y) (hs : s.SingleFiber y z) : (r.compose s).SingleFiber x z := by
  refine ⟨?_,?_⟩
  · rw [compose_get,hs.1,hr.1]
  · intro E b hb
    rw [compose_get] at hb
    exact hs.2 b (hr.2 _ hb)

theorem parallel_last_singleFiber {F U : List (NormalForm P)} (r : Route F U) (C : NormalForm P) :
    (r.parallel (identity [C])).SingleFiber (At.shift F (.here C [])) (At.shift U (.here C [])) := by
  refine ⟨?_,?_⟩
  · rw [parallel_shift,get_identity]
  · intro E b hb
    cases At.cases_append U [C] b with
    | inl h =>
      obtain ⟨b,rfl⟩ := h
      rw [parallel_before,At.index_before,At.index_shift,At.index,Nat.add_zero] at hb
      have hi := (r.get b).index_lt
      omega
    | inr h =>
      obtain ⟨b,rfl⟩ := h
      cases b with
      | here => rfl
      | there b => cases b

end Route
namespace StructuralProgram

theorem seq_singleFiber {F U V : List (NormalForm P)} {C : NormalForm P}
    (p : StructuralProgram P F U) (q : StructuralProgram P U V)
    (x : At F C) (y : At U C) (z : At V C)
    (hp : p.route.SingleFiber x y) (hq : q.route.SingleFiber y z) :
    (p.seq q).route.SingleFiber x z := by
  refine ⟨?_,?_⟩
  · rw [route_get]
    change p.get (q.get z) = x
    have hq' : q.get z = y := by simpa only [route_get] using hq.1
    rw [hq']
    simpa only [route_get] using hp.1
  · intro E b hb
    rw [route_get] at hb
    change (p.get (q.get b)).index = x.index at hb
    apply hq.2
    rw [route_get]
    apply hp.2
    rw [route_get]
    exact hb

theorem consFixed_singleFiber {F U : List (NormalForm P)} (p : StructuralProgram P F U) (C : NormalForm P) :
    (p.consFixed C).route.SingleFiber (.here C F) (.here C U) := by
  refine ⟨?_,?_⟩
  · rw [route_get,consFixed_here]
  · intro E b hb
    rw [route_get] at hb
    cases b with
    | here => rfl
    | there b => rw [consFixed_there] at hb; simp only [At.index] at hb; omega

theorem suffixFixed_singleFiber {F U : List (NormalForm P)} {C : NormalForm P}
    (p : StructuralProgram P F U) (x : At F C) (y : At U C) (hp : p.route.SingleFiber x y)
    (I : List (NormalForm P)) : (p.suffixFixed I).route.SingleFiber (x.before I) (y.before I) := by
  refine ⟨?_,?_⟩
  · rw [route_get,suffixFixed_before,← route_get,hp.1]
  · intro E b hb
    rw [route_get] at hb
    cases At.cases_append U I b with
    | inl h =>
      obtain ⟨b,rfl⟩ := h
      rw [suffixFixed_before,At.index_before,At.index_before] at hb
      rw [At.index_before,At.index_before]
      exact hp.2 b (by rw [route_get]; exact hb)
    | inr h =>
      obtain ⟨b,rfl⟩ := h
      rw [suffixFixed_shift,At.index_shift,At.index_before] at hb
      have hi := x.index_lt
      omega

theorem residual_singleFiber {F U : List (NormalForm P)} {C Q : NormalForm P}
    (p : StructuralProgram P F U) (x : At F C) (y : At U C) (hp : p.route.SingleFiber x y)
    (v : At x.erase Q) (w : At y.erase Q)
    (hq : p.route.SingleFiber (x.retain v) (y.retain w)) :
    (p.residual x y hp).route.SingleFiber v w := by
  have hget {E : NormalForm P} (a : At y.erase E) :
      x.retain ((p.residual x y hp).route.get a) = p.route.get (y.retain a) := by
    rw [route_get,residual,Route.program_get]
    exact Route.residual_get _ _ _ _ _
  refine ⟨?_,?_⟩
  · apply x.retain_injective _ _
    rw [hget,hq.1]
  · intro E b hb
    have h := hget b
    have he := ((p.residual x y hp).route.get b).formula_eq v hb
    cases he
    have he := At.index_injective _ _ hb
    rw [he] at h
    have hi := hq.2 (y.retain b) (congrArg At.index h.symm)
    have he := (y.retain b).formula_eq (y.retain w) hi
    cases he
    have he := y.retain_injective _ _ (At.index_injective _ _ hi)
    exact congrArg At.index he

end StructuralProgram
end DosenPetric.Reduced.Gentzen
