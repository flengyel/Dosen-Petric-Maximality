module

public import DosenPetric.GentzenContractionBlocks

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

/-- A nonempty positional selection. `more` deletes an earlier selected copy;
`last` retains the last selected copy. `fixed` preserves an unselected tag. -/
inductive ContractionSelection (C : NormalForm P) :
    List (NormalForm P) → List (NormalForm P) → Type u where
  | last (Θ : List (NormalForm P)) : ContractionSelection C (C :: Θ) (C :: Θ)
  | fixed {F K} (A : NormalForm P) :
      ContractionSelection C F K → ContractionSelection C (A :: F) (A :: K)
  | more {F K} : ContractionSelection C F K → ContractionSelection C (C :: F) K

namespace ContractionSelection
variable {C : NormalForm P} {F I K : List (NormalForm P)}

def keep : {F K : List (NormalForm P)} → ContractionSelection C F K → At K C
  | _,_,.last Θ => .here C Θ
  | _,_,.fixed _ p => p.keep.there
  | _,_,.more p => p.keep

def selected : {F K : List (NormalForm P)} → ContractionSelection C F K → List (At F C)
  | _,_,.last Θ => [.here C Θ]
  | _,_,.fixed _ p => p.selected.map At.there
  | _,_,.more p => .here C _ :: p.selected.map At.there

def arity : {F K : List (NormalForm P)} → ContractionSelection C F K → Nat
  | _,_,.last _ => 1
  | _,_,.fixed _ p => p.arity
  | _,_,.more p => p.arity + 1

theorem selected_length (p : ContractionSelection C F K) : p.selected.length = p.arity := by
  induction p with
  | last => rfl
  | fixed A p ih => simp only [selected,List.length_map,arity,ih]
  | more p ih => simp only [selected,List.length_cons,List.length_map,arity,ih]

def route : {F K : List (NormalForm P)} → ContractionSelection C F K → Route K F
  | _,_,.last Θ => Route.identity (C :: Θ)
  | _,_,.fixed A p => .cons (.here A _) (p.route.map (fun a => a.there))
  | _,_,.more p => .cons p.keep p.route

def first : {F K : List (NormalForm P)} → ContractionSelection C F K → List (NormalForm P)
  | _,_,.last _ => []
  | _,_,.fixed A p => A :: p.first
  | _,_,.more _ => []

def rest : {F K : List (NormalForm P)} → ContractionSelection C F K → List (List (NormalForm P))
  | _,_,.last _ => []
  | _,_,.fixed _ p => p.rest
  | _,_,.more p => p.first :: p.rest

def tail : {F K : List (NormalForm P)} → ContractionSelection C F K → List (NormalForm P)
  | _,_,.last Θ => Θ
  | _,_,.fixed _ p => p.tail
  | _,_,.more p => p.tail

abbrev gs (p : ContractionSelection C F K) := p.first :: p.rest

theorem upper (p : ContractionSelection C F K) : repeated C p.gs ++ p.tail = F := by
  induction p with
  | last => rfl
  | fixed A p ih => simpa only [gs,first,rest,tail,repeated,List.cons_append] using congrArg (List.cons A) ih
  | more p ih => simpa only [gs,first,rest,tail,repeated,List.nil_append,List.cons_append] using congrArg (List.cons C) ih

theorem lower (p : ContractionSelection C F K) : gaps p.gs ++ C :: p.tail = K := by
  induction p with
  | last => rfl
  | fixed A p ih => simpa only [gs,first,rest,tail,gaps,List.cons_append] using congrArg (List.cons A) ih
  | more p ih => simpa only [gs,first,rest,tail,gaps,List.nil_append] using ih

theorem count (p : ContractionSelection C F K) : p.gs.length = p.arity := by
  induction p with
  | last => rfl
  | fixed A p ih => exact ih
  | more p ih => simpa only [gs,rest,List.length_cons,arity] using congrArg (fun n => n+1) ih

abbrev block (p : ContractionSelection C F K) : ContractionBlock P F K :=
  ⟨C,p.gs,p.tail,p.upper,p.lower⟩

def fuse : {F I K : List (NormalForm P)} → (p : ContractionSelection C F I) →
    (q : ContractionSelection C I K) → p.keep ∈ q.selected → ContractionSelection C F K
  | _,_,_,.last _,q,_ => q
  | _,_,_,.more p,q,h => .more (fuse p q h)
  | _,_,_,.fixed _ p,.last _,h => False.elim (by simp only [keep,selected,List.mem_singleton,reduceCtorEq] at h)
  | _,_,_,.fixed _ p,.more q,h => .more (fuse p q (by
      simpa only [keep,selected,List.mem_cons,At.there.injEq,reduceCtorEq,false_or,
        TraceRoute.mem_there] using h))
  | _,_,_,.fixed A p,.fixed _ q,h => .fixed A (fuse p q (by
      simpa only [keep,selected,TraceRoute.mem_there] using h))

theorem selected_iff (p : ContractionSelection C F K) (a : At F C) :
    a ∈ p.selected ↔ p.route.get a = p.keep := by
  induction p with
  | last Θ => simp only [selected,List.mem_singleton,route,Route.get_identity,keep]
  | fixed A p ih =>
    cases a with
    | here => simp [selected,route,Route.get,keep,List.mem_map]
    | there a => simpa only [selected,route,Route.get,Route.get_map,keep,At.there.injEq,
        TraceRoute.mem_there] using ih a
  | more p ih =>
    cases a with
    | here => simp [selected,route,Route.get,keep]
    | there a => simpa only [selected,route,Route.get,keep,List.mem_cons,reduceCtorEq,false_or,
        TraceRoute.mem_there] using ih a

theorem fuse_keep (p : ContractionSelection C F I) (q : ContractionSelection C I K)
    (h : p.keep ∈ q.selected) : (fuse p q h).keep = q.keep := by
  induction p generalizing K with
  | last => rfl
  | more p ih => exact ih q h
  | fixed A p ih =>
    cases q with
    | last => simp [keep,selected] at h
    | more q => exact ih q _
    | fixed A q => exact congrArg At.there (ih q _)

theorem fuse_count (p : ContractionSelection C F I) (q : ContractionSelection C I K)
    (h : p.keep ∈ q.selected) : (fuse p q h).arity + 1 = p.arity + q.arity := by
  induction p generalizing K with
  | last => simp only [fuse,arity]; omega
  | more p ih => have hh := ih q h; simp only [fuse,arity]; omega
  | fixed A p ih =>
    cases q with
    | last => simp [keep,selected] at h
    | more q =>
      have hh := ih q (by simpa only [keep,selected,List.mem_cons,reduceCtorEq,false_or,TraceRoute.mem_there] using h)
      simp only [fuse,arity]
      omega
    | fixed A q => exact ih q _

theorem fuse_get (p : ContractionSelection C F I) (q : ContractionSelection C I K)
    (h : p.keep ∈ q.selected) {A : NormalForm P} (a : At F A) :
    (fuse p q h).route.get a = q.route.get (p.route.get a) := by
  induction p generalizing K with
  | last => simp only [fuse,route,Route.get_identity]
  | more p ih =>
    cases a with
    | here => exact (fuse_keep p q h).trans ((q.selected_iff p.keep).mp h).symm
    | there a => exact ih q h a
  | fixed B p ih =>
    cases q with
    | last => simp [keep,selected] at h
    | more q =>
      cases a with
      | here => exact fuse_keep p q _
      | there a => simpa only [fuse,route,Route.get,Route.get_map] using ih q _ a
    | fixed B q =>
      cases a with
      | here => rfl
      | there a => simpa only [fuse,route,Route.get,Route.get_map] using congrArg At.there (ih q _ a)

end ContractionSelection
end DosenPetric.Reduced.Gentzen
