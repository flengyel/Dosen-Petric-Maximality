module

public import DosenPetric.GentzenSelectedExtraction
public import DosenPetric.GentzenContractionPrepend

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.ContractionSelection
universe u
variable {P : Type u} {C : NormalForm P}

theorem arity_pos {F K : List (NormalForm P)} (p : ContractionSelection C F K) :
    0 < p.arity := by
  induction p with
  | last => exact Nat.zero_lt_succ _
  | fixed A p ih => exact ih
  | more p ih => change 0 < p.arity+1; omega

theorem selected_nonempty {F K : List (NormalForm P)} (p : ContractionSelection C F K) :
    p.selected ≠ [] := by
  intro he
  have hn := p.arity_pos
  have hl := p.selected_length
  rw [he] at hl
  simp only [List.length_nil] at hl
  omega

theorem selected_contains_zero {F K : List (NormalForm P)}
    (p : ContractionSelection C F K) :
    ∀ (a : At F C), a ∈ p.selected → a.index = 0 →
      ∃ Θ, F = C::Θ := by
  intro a _ ha
  cases a with
  | here => exact ⟨_,rfl⟩
  | there a => simp only [At.index] at ha; omega

/-- Fixed context left after deleting every selected copy, including the
    retained one. This is a context operation, not an arrow. -/
@[reducible] def erased : {F K : List (NormalForm P)} → ContractionSelection C F K → List (NormalForm P)
  | _,_,.last Θ => Θ
  | _,_,.fixed A p => A::p.erased
  | _,_,.more p => p.erased

theorem erased_eq {F K : List (NormalForm P)} (p : ContractionSelection C F K) :
    p.erased = gaps p.gs++p.tail := by
  induction p with
  | last => rfl
  | fixed A p ih => simpa only [erased,gs,first,rest,gaps,tail,List.cons_append] using congrArg (List.cons A) ih
  | more p ih => simpa only [erased,gs,first,rest,gaps,tail,List.nil_append] using ih

/-- Concatenate two nonempty positional selections, retaining the last
    selected copy of the second context. -/
def chain {F K U L : List (NormalForm P)} (p : ContractionSelection C F K)
    (q : ContractionSelection C U L) : ContractionSelection C (F++U) (p.erased++L) :=
  match p with
  | .last Θ => .more (q.prependFixed Θ)
  | .fixed A p => .fixed A (chain p q)
  | .more p => .more (chain p q)

theorem chain_keep {F K U L : List (NormalForm P)} (p : ContractionSelection C F K)
    (q : ContractionSelection C U L) : (p.chain q).keep = At.shift p.erased q.keep := by
  induction p with
  | last => exact prepend_keep ..
  | fixed A p ih => exact congrArg At.there ih
  | more p ih => exact ih

theorem chain_count {F K U L : List (NormalForm P)} (p : ContractionSelection C F K)
    (q : ContractionSelection C U L) : (p.chain q).arity = p.arity+q.arity := by
  induction p with
  | last Θ =>
    rw [chain,arity]
    have h := prepend_count q Θ
    rw [count,count] at h
    change (prependFixed _ q).arity+1 = 1+q.arity
    omega
  | fixed A p ih => exact ih
  | more p ih =>
    change (p.chain q).arity+1 = (p.arity+1)+q.arity
    rw [ih]
    omega

theorem chain_selected {F K U L : List (NormalForm P)} (p : ContractionSelection C F K)
    (q : ContractionSelection C U L) :
    (p.chain q).selected =
      p.selected.map (fun a => a.before U) ++ q.selected.map (At.shift F) := by
  induction p with
  | last Θ =>
    change .here C (Θ++U)::((q.prependFixed Θ).selected.map At.there) = _
    rw [prepend_selected]
    simp only [selected,List.map_map,Function.comp_def,List.map_cons,
      List.map_nil,List.singleton_append,At.before]
    rfl
  | fixed A p ih =>
    simp only [chain,selected,ih,List.map_append,List.map_map,Function.comp_def]
    rfl
  | more p ih =>
    change .here C _ :: ((p.chain q).selected.map At.there) = _
    rw [ih]
    simp only [selected,List.map_append,List.map_cons,
      List.map_map,Function.comp_def,List.cons_append]
    rfl

theorem chain_shift {F K U L : List (NormalForm P)} (p : ContractionSelection C F K)
    (q : ContractionSelection C U L) {A : NormalForm P} (a : At U A) :
    (p.chain q).route.get (At.shift F a) = At.shift p.erased (q.route.get a) := by
  induction p with
  | last Θ =>
    change (q.prependFixed Θ).route.get (At.shift Θ a) = At.shift Θ (q.route.get a)
    exact prepend_shift ..
  | fixed B p ih => simpa only [chain,route,Route.get,Route.get_map,At.shift,erased] using congrArg At.there ih
  | more p ih => exact ih

theorem there_lists {Γ : List (NormalForm P)} {A : NormalForm P}
    (xs ys : List (At Γ C))
    (h : xs.map (@At.there P C A Γ) = ys.map At.there) : xs = ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> cases h; rfl
  | cons a xs ih =>
    cases ys with
    | nil => cases h
    | cons b ys =>
      have he := List.cons.inj h
      cases At.there.inj he.1
      exact congrArg (List.cons a) (ih ys he.2)

theorem ext_selected {F K : List (NormalForm P)} (p q : ContractionSelection C F K)
    (h : p.selected = q.selected) : p = q := by
  induction p with
  | last Θ =>
    cases q with
    | last => rfl
    | fixed A q =>
      have hx : (.here C Θ) ∈ (fixed C q).selected := by rw [←h]; exact List.mem_cons_self
      obtain ⟨a,_,he⟩ := List.mem_map.mp hx
      cases he
    | more q =>
      have he := (List.cons.inj h).2
      have hn : q.selected = [] := List.map_eq_nil_iff.mp he.symm
      exact False.elim (q.selected_nonempty hn)
  | fixed A p ih =>
    cases q with
    | last Θ =>
      have hx : (.here C _) ∈ (fixed C p).selected := by rw [h]; exact List.mem_cons_self
      obtain ⟨a,_,he⟩ := List.mem_map.mp hx
      cases he
    | fixed A q => exact congrArg (fixed A) (ih q (there_lists _ _ h))
    | more q =>
      have hx : (.here C _) ∈ (fixed C p).selected := by rw [h]; exact List.mem_cons_self
      obtain ⟨a,_,he⟩ := List.mem_map.mp hx
      cases he
  | more p ih =>
    cases q with
    | last Θ =>
      have he := (List.cons.inj h).2
      have hn : p.selected = [] := List.map_eq_nil_iff.mp he
      exact False.elim (p.selected_nonempty hn)
    | fixed A q =>
      have hx : (.here C _) ∈ (fixed C q).selected := by rw [←h]; exact List.mem_cons_self
      obtain ⟨a,_,he⟩ := List.mem_map.mp hx
      cases he
    | more q => exact congrArg more (ih q (there_lists _ _ (List.cons.inj h).2))

end DosenPetric.Reduced.Gentzen.ContractionSelection
