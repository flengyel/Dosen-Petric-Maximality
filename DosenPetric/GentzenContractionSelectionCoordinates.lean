module

public import DosenPetric.GentzenContractionSelection

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

namespace Route
theorem ext_get {Γ Δ : List (NormalForm P)} (w v : Route Γ Δ)
    (h : ∀ {A : NormalForm P} (a : At Δ A), w.get a = v.get a) : w = v := by
  induction w with
  | nil => cases v; rfl
  | @cons A Δ a w ih =>
    cases v with
    | cons b v =>
      have hab : a = b := h (.here A Δ)
      cases hab
      exact congrArg (Route.cons a) (ih v (fun x => h x.there))
end Route

namespace ContractionSelection
variable {C : NormalForm P} {F K : List (NormalForm P)}

theorem keep_index (p : ContractionSelection C F K) : p.keep.index = (gaps p.gs).length := by
  induction p with
  | last => rfl
  | fixed A p ih =>
    simp only [keep,At.index,first,rest,gaps,List.length_append,List.length_cons] at *
    omega
  | more p ih => simpa only [keep,gs,first,rest,gaps,List.nil_append] using ih

theorem copyIndex_front (A : NormalForm P) (Γ : List (NormalForm P))
    (gs : List (List (NormalForm P))) (i : Nat) :
    copyIndex ((A::Γ)::gs) (i+1) = copyIndex (Γ::gs) i+1 := by
  simp only [copyIndex,List.length_cons]
  by_cases h : i < Γ.length
  · rw [ite_eq_left h,ite_eq_left (by omega)]
  · rw [ite_eq_right h,ite_eq_right (by omega)]
    by_cases e : i = Γ.length
    · rw [ite_eq_left e,ite_eq_left (by omega)]; omega
    · rw [ite_eq_right e,ite_eq_right (by omega)]
      have he : i+1-(Γ.length+1)-1 = i-Γ.length-1 := by omega
      rw [he]; omega

theorem get_index (p : ContractionSelection C F K) {A : NormalForm P} (a : At F A) :
    (p.route.get a).index = copyIndex p.gs a.index := by
  induction p with
  | last Θ =>
    cases a with
    | here => rfl
    | there a =>
      rw [route,Route.get_identity]
      change a.index+1 = copyIndex [[]] (a.index+1)
      simp only [copyIndex,List.length_nil,Nat.not_lt_zero,ite_false,gaps,Nat.zero_add]
      rw [ite_eq_right (by omega)]
      omega
  | fixed B p ih =>
    cases a with
    | here => simp [route,Route.get,first,copyIndex,At.index]
    | there a =>
      simp only [route,Route.get,Route.get_map,At.index]
      change (p.route.get a).index+1 = copyIndex ((B::p.first)::p.rest) (a.index+1)
      rw [copyIndex_front,ih a]
  | more p ih =>
    cases a with
    | here =>
      change p.keep.index = copyIndex ([]::p.gs) 0
      rw [copyIndex]
      simpa only [List.length_nil,Nat.lt_irrefl,ite_false,ite_true,Nat.zero_add] using p.keep_index
    | there a =>
      change (p.route.get a).index = copyIndex ([]::p.gs) (a.index+1)
      rw [copyIndex]
      simp only [List.length_nil,Nat.not_lt_zero,ite_false,Nat.zero_add]
      rw [ite_eq_right (by omega)]
      have hi : a.index+1-0-1 = a.index := by omega
      rw [hi]
      exact ih a

theorem keep_eq (p : ContractionSelection C F K) : p.keep = p.block.keep :=
  At.index_injective _ _ (p.keep_index.trans p.block.keep_index.symm)

theorem route_eq (p : ContractionSelection C F K) : p.route = p.block.route := by
  apply Route.ext_get
  intro A a
  exact At.index_injective _ _ ((p.get_index a).trans (p.block.get_index a).symm)

theorem selected_ordered (p : ContractionSelection C F K) : At.Ordered p.selected := by
  induction p with
  | last => exact .cons (by intro a h; cases h) .nil
  | fixed A p ih => exact At.ordered_there ih
  | more p ih =>
    apply List.Pairwise.cons
    · intro a ha
      obtain ⟨b,_,rfl⟩ := List.mem_map.mp ha
      simp only [At.index]; omega
    · exact At.ordered_there ih

theorem selected_eq (p : ContractionSelection C F K) : p.selected = p.block.selected := by
  apply At.ordered_ext _ _ p.selected_ordered p.block.selected_ordered
  intro a
  rw [p.selected_iff,p.block.selected_iff,p.route_eq,p.keep_eq]

def cast {F' K' : List (NormalForm P)} (hF : F = F') (hK : K = K')
    (p : ContractionSelection C F K) : ContractionSelection C F' K' := hF ▸ hK ▸ p

theorem first_cast {F' K' : List (NormalForm P)} (hF : F = F') (hK : K = K')
    (p : ContractionSelection C F K) : (p.cast hF hK).first = p.first := by cases hF; cases hK; rfl
theorem rest_cast {F' K' : List (NormalForm P)} (hF : F = F') (hK : K = K')
    (p : ContractionSelection C F K) : (p.cast hF hK).rest = p.rest := by cases hF; cases hK; rfl
theorem tail_cast {F' K' : List (NormalForm P)} (hF : F = F') (hK : K = K')
    (p : ContractionSelection C F K) : (p.cast hF hK).tail = p.tail := by cases hF; cases hK; rfl

def prependFixed (Γ : List (NormalForm P)) (p : ContractionSelection C F K) :
    ContractionSelection C (Γ++F) (Γ++K) := match Γ with
  | [] => p
  | A::Γ => .fixed A (prependFixed Γ p)

theorem first_prependFixed (Γ : List (NormalForm P)) (p : ContractionSelection C F K) :
    (prependFixed Γ p).first = Γ++p.first := by
  induction Γ with
  | nil => rfl
  | cons A Γ ih => exact congrArg (List.cons A) ih
theorem rest_prependFixed (Γ : List (NormalForm P)) (p : ContractionSelection C F K) :
    (prependFixed Γ p).rest = p.rest := by induction Γ <;> simp_all only [prependFixed,rest]
theorem tail_prependFixed (Γ : List (NormalForm P)) (p : ContractionSelection C F K) :
    (prependFixed Γ p).tail = p.tail := by induction Γ <;> simp_all only [prependFixed,tail]

def ofGaps (C : NormalForm P) (Γ : List (NormalForm P)) :
    (gs : List (List (NormalForm P))) → (Θ : List (NormalForm P)) →
    ContractionSelection C (repeated C (Γ::gs)++Θ) (gaps (Γ::gs)++C::Θ)
  | [],Θ => (prependFixed Γ (.last Θ)).cast
      (by simp only [repeated,List.nil_append,List.cons_append,List.append_assoc])
      (by simp only [gaps,List.append_nil])
  | Δ::gs,Θ => (prependFixed Γ (.more (ofGaps C Δ gs Θ))).cast
      (copyTarget C Γ (Δ::gs) Θ) (copySource C Γ (Δ::gs) Θ)

theorem ofGaps_gs (Γ : List (NormalForm P)) (gss : List (List (NormalForm P)))
    (Θ : List (NormalForm P)) : (ofGaps C Γ gss Θ).gs = Γ::gss := by
  induction gss generalizing Γ with
  | nil => simp only [ofGaps,ContractionSelection.gs,first_cast,rest_cast,first_prependFixed,rest_prependFixed,first,rest,List.append_nil]
  | cons Δ gs ih =>
    have h := ih Δ
    simp only [ofGaps,ContractionSelection.gs,first_cast,rest_cast,first_prependFixed,rest_prependFixed,first,rest,List.append_nil]
    exact congrArg (List.cons Γ) h

theorem ofGaps_tail (Γ : List (NormalForm P)) (gs : List (List (NormalForm P)))
    (Θ : List (NormalForm P)) : (ofGaps C Γ gs Θ).tail = Θ := by
  induction gs generalizing Γ with
  | nil => simp only [ofGaps,tail_cast,tail_prependFixed,tail]
  | cons Δ gs ih => simp only [ofGaps,tail_cast,tail_prependFixed,tail]; exact ih Δ

theorem gs_cast {F' K' : List (NormalForm P)} (hF : F = F') (hK : K = K')
    (p : ContractionSelection C F K) : (p.cast hF hK).gs = p.gs := by
  change (p.cast hF hK).first :: (p.cast hF hK).rest = p.first :: p.rest
  rw [first_cast,rest_cast]

def ofList (C : NormalForm P) : (gss : List (List (NormalForm P))) →
    (Θ : List (NormalForm P)) → gss ≠ [] →
    ContractionSelection C (repeated C gss++Θ) (gaps gss++C::Θ)
  | [],_,h => False.elim (h rfl)
  | Γ::gss,Θ,_ => ofGaps C Γ gss Θ

theorem ofList_gs (gss : List (List (NormalForm P))) (Θ : List (NormalForm P)) (h : gss ≠ []) :
    (ofList C gss Θ h).gs = gss := by
  cases gss with
  | nil => exact False.elim (h rfl)
  | cons Γ gss => exact ofGaps_gs Γ gss Θ

theorem ofList_tail (gss : List (List (NormalForm P))) (Θ : List (NormalForm P)) (h : gss ≠ []) :
    (ofList C gss Θ h).tail = Θ := by
  cases gss with
  | nil => exact False.elim (h rfl)
  | cons Γ gss => exact ofGaps_tail Γ gss Θ

theorem block_match (p : ContractionSelection C F K) (b : ContractionBlock P F K)
    (hc : b.C = C) (hg : p.gs = b.gs) (ht : p.tail = b.tail) : p.block = b := by
  cases b with
  | mk B gss Θ hu hl =>
    change B = C at hc
    change p.gs = gss at hg
    change p.tail = Θ at ht
    cases hc
    cases hg
    cases ht
    rfl

end ContractionSelection

namespace ContractionBlock
variable {F K : List (NormalForm P)} (b : ContractionBlock P F K)

def selection (h : b.gs ≠ []) : ContractionSelection b.C F K :=
  (ContractionSelection.ofList b.C b.gs b.tail h).cast b.upper b.lower

theorem selection_block (h : b.gs ≠ []) : (b.selection h).block = b := by
  apply ContractionSelection.block_match _ b rfl
  · exact (ContractionSelection.gs_cast ..).trans (ContractionSelection.ofList_gs ..)
  · exact (ContractionSelection.tail_cast ..).trans (ContractionSelection.ofList_tail ..)

end ContractionBlock
end DosenPetric.Reduced.Gentzen
