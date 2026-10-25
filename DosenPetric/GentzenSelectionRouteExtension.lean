module

public import DosenPetric.GentzenSelectionAssociativity
public import DosenPetric.GentzenParallelRoutes

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u} {C : NormalForm P}
namespace ContractionSelection
variable {F K : List (NormalForm P)}

theorem extend_before (p : ContractionSelection C F K) (Ξ : List (NormalForm P))
    {A : NormalForm P} (a : At F A) :
    (p.extend Ξ).route.get (a.before Ξ)=(p.route.get a).before Ξ := by
  induction p with
  | last Θ =>
    change (Route.identity (C::(Θ++Ξ))).get (a.before Ξ)=((Route.identity (C::Θ)).get a).before Ξ
    rw [Route.get_identity,Route.get_identity]
  | fixed B p ih =>
    cases a with
    | here => rfl
    | there a => simpa only [extend,route,Route.get,Route.get_map,At.before] using congrArg At.there (ih a)
  | more p ih =>
    cases a with
    | here => exact p.extend_keep Ξ
    | there a => exact ih a

theorem extend_shift (p : ContractionSelection C F K) (Ξ : List (NormalForm P))
    {A : NormalForm P} (a : At Ξ A) :
    (p.extend Ξ).route.get (At.shift F a)=At.shift K a := by
  induction p with
  | last => exact Route.get_identity _
  | fixed B p ih => simpa only [extend,route,Route.get,Route.get_map,At.shift] using congrArg At.there ih
  | more p ih => exact ih

theorem extend_route (p : ContractionSelection C F K) (Ξ : List (NormalForm P)) :
    (p.extend Ξ).route=p.route.parallel (Route.identity Ξ) := by
  apply Route.ext_get
  intro A a
  cases At.cases_append F Ξ a with
  | inl h => obtain ⟨a,rfl⟩:=h; rw [extend_before,Route.parallel_before]
  | inr h => obtain ⟨a,rfl⟩:=h; rw [extend_shift,Route.parallel_shift,Route.get_identity]

theorem route_cast {F' K' : List (NormalForm P)} (p : ContractionSelection C F K)
    (hF : F=F') (hK : K=K') : (p.cast hF hK).route=p.route.cast hK hF := by
  cases hF; cases hK; rfl
end ContractionSelection

namespace Route
variable {F K U L V J : List (NormalForm P)}

def compose (p : Route K U) (q : Route U F) : Route K F := q.map (fun a => p.get a)

theorem compose_get (p : Route K U) (q : Route U F) {A : NormalForm P} (a : At F A) :
    (p.compose q).get a=p.get (q.get a) := by rw [compose,get_map]

theorem compose_side (o : Op) (p : Route K U) (q : Route U F) :
    (p.compose q).sideArrow o=(side P o).comp (p.sideArrow o) (q.sideArrow o) := by
  apply side_ext o
  intro A a
  rw [sideArrow_get,(side P o).assoc,sideArrow_get,sideArrow_get,compose_get]

theorem parallel_assoc (p : Route K F) (q : Route L U) (r : Route J V) :
    ((p.parallel q).parallel r).cast (List.append_assoc K L J) (List.append_assoc F U V) =
      p.parallel (q.parallel r) := by
  apply ext_get
  intro A a
  apply At.index_injective
  rw [get_cast,At.index_cast]
  cases At.cases_append F (U++V) a with
  | inl h =>
    obtain ⟨a,rfl⟩:=h
    have he : (a.before (U++V)).cast (List.append_assoc F U V).symm=(a.before U).before V := by
      apply At.index_injective; simp only [At.index_cast,At.index_before]
    rw [he,parallel_before,parallel_before,parallel_before]
    simp only [At.index_before]
  | inr h =>
    obtain ⟨a,rfl⟩:=h
    cases At.cases_append U V a with
    | inl h =>
      obtain ⟨a,rfl⟩:=h
      have he : (At.shift F (a.before V)).cast (List.append_assoc F U V).symm=
          (At.shift F a).before V := by
        apply At.index_injective; simp only [At.index_cast,At.index_before,At.index_shift]
      rw [he,parallel_before,parallel_shift,parallel_shift,parallel_before]
      simp only [At.index_before,At.index_shift]
    | inr h =>
      obtain ⟨a,rfl⟩:=h
      have he : (At.shift F (At.shift U a)).cast (List.append_assoc F U V).symm=
          At.shift (F++U) a := by
        apply At.index_injective; simp only [At.index_cast,At.index_shift,List.length_append]; omega
      rw [he,parallel_shift,parallel_shift,parallel_shift]
      simp only [At.index_shift,List.length_append]; omega

theorem cast_factor {F' U' : List (NormalForm P)}
    (p : Route K F) (q : Route K U) (r : Route U F) (o : Op)
    (h : p.sideArrow o=(side P o).comp (q.sideArrow o) (r.sideArrow o))
    (hF : F=F') (hU : U=U') :
    (p.cast rfl hF).sideArrow o=(side P o).comp
      ((q.cast rfl hU).sideArrow o) ((r.cast hU hF).sideArrow o) := by
  cases hF; cases hU; exact h
end Route
end DosenPetric.Reduced.Gentzen
