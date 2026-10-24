module

public import DosenPetric.GentzenUnaryCasts

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.SelectedThinning
universe u
variable {P : Type u}

theorem copyIndex_old (C : NormalForm P) (gs : List (List (NormalForm P)))
    (Θ : List (NormalForm P)) (i : Nat) (hi : i < (repeated C gs++Θ).length) :
    copyIndex (gs++[Θ]) i = exchangeIndex (gaps gs).length 1 Θ.length (copyIndex gs i) := by
  induction gs generalizing i with
  | nil =>
    simp only [List.nil_append,repeated,List.nil_append] at hi
    simp only [List.nil_append,copyIndex,gaps,List.length_nil,Nat.zero_add,exchangeIndex]
    repeat first | split | omega
  | cons Γ gs ih =>
    have hg : (gaps (gs++[Θ])).length = (gaps gs).length+Θ.length := by
      simp only [GapInsertion.gaps_append,gaps,List.append_nil,List.length_append]
    simp only [repeated,List.length_append,List.length_cons] at hi
    simp only [List.cons_append,gaps,List.length_append]
    by_cases h : i < Γ.length
    · rw [copyIndex,ite_eq_left h,copyIndex,ite_eq_left h]
      exact (GapExchange.exchange_prefix Γ.length (gaps gs).length 1 Θ.length i h).symm
    · by_cases e : i = Γ.length
      · subst i
        rw [copyIndex,ite_eq_right (Nat.lt_irrefl _),ite_eq_left rfl,
          copyIndex,ite_eq_right (Nat.lt_irrefl _),ite_eq_left rfl,hg]
        unfold exchangeIndex
        repeat first | split | omega
      · rw [copyIndex,ite_eq_right h,ite_eq_right e,copyIndex,ite_eq_right h,ite_eq_right e]
        have he := ih (i-Γ.length-1) (by simp only [List.length_append]; omega)
        rw [he,GapExchange.exchange_add]

theorem copyIndex_last (C : NormalForm P) (gs : List (List (NormalForm P)))
    (Θ : List (NormalForm P)) :
    copyIndex (gs++[Θ]) (repeated C gs++Θ).length = (gaps gs).length+Θ.length := by
  induction gs with
  | nil =>
    simp only [List.nil_append,repeated,List.nil_append,copyIndex,gaps,List.length_nil,
      Nat.lt_irrefl,ite_false,ite_true,Nat.zero_add,Nat.add_zero]
  | cons Γ gs ih =>
    simp only [List.cons_append,repeated,gaps,List.length_append,List.length_cons]
    rw [copyIndex,ite_eq_right (by omega),ite_eq_right (by omega)]
    have he : Γ.length+((repeated C gs).length+1)+Θ.length-Γ.length-1 =
        (repeated C gs++Θ).length := by simp only [List.length_append]; omega
    rw [he,ih]
    omega

/-- Original data only; the routing, list, and rank conclusions are derived. -/
structure Data (P : Type u) where
  C : NormalForm P
  gs : List (List (NormalForm P))
  Θ : List (NormalForm P)

namespace Data
variable (d : Data P)
abbrev F := repeated d.C d.gs ++ d.Θ
abbrev I := gaps d.gs ++ d.C :: d.Θ
abbrev U := d.F ++ [d.C]
abbrev K := (gaps d.gs ++ d.Θ) ++ [d.C]
abbrev outerGaps := d.gs ++ [d.Θ]

theorem thinSource : d.F++[] = d.F := List.append_nil _
theorem outerSource : repeated d.C d.outerGaps++[] = d.U := by
  simp only [outerGaps,GapInsertion.repeated_append,repeated,List.append_nil,
    List.append_assoc]
theorem outerTarget : gaps d.outerGaps++d.C::[] = d.K := by
  simp only [outerGaps,GapInsertion.gaps_append,gaps,List.append_nil]
theorem exchangeSource : gaps d.gs++[d.C]++d.Θ++[] = d.I := by
  simp only [List.append_nil,List.append_assoc,List.cons_append,List.nil_append]
theorem exchangeTarget : gaps d.gs++d.Θ++[d.C]++[] = d.K := List.append_nil _
theorem outer_count : d.outerGaps.length = d.gs.length+1 := by
  simp only [outerGaps,List.length_append,List.length_cons,List.length_nil]
theorem outer_bound (hn : 2 ≤ d.gs.length) : 2 ≤ d.outerGaps.length := by rw [d.outer_count]; omega

abbrev inner : ContractionBlock P d.F d.I := ⟨d.C,d.gs,d.Θ,rfl,rfl⟩
abbrev outer : ContractionBlock P d.U d.K := ⟨d.C,d.outerGaps,[],d.outerSource,d.outerTarget⟩
def t : Route d.U d.F := (Route.thin d.F [] d.C).cast rfl d.thinSource
def e : Route d.K d.I := (Route.exchange (gaps d.gs) [d.C] d.Θ []).cast d.exchangeTarget d.exchangeSource
def z : At d.U d.C := At.shift d.F (.here d.C [])
abbrev x := d.outer.keep

theorem t_index {A : NormalForm P} (a : At d.F A) : (d.t.get a).index = a.index := by
  rw [t,Route.get_index_cast,thin_index,At.index_cast]
  exact ite_eq_left a.index_lt
theorem z_index : d.z.index = d.F.length := by
  simp only [z,At.index_shift,At.index,Nat.add_zero]
theorem x_index : d.x.index = (gaps d.gs).length+d.Θ.length := by
  rw [ContractionBlock.keep_index]
  simp only [outerGaps,GapInsertion.gaps_append,gaps,List.append_nil,List.length_append]
theorem e_index {A : NormalForm P} (a : At d.I A) :
    (d.e.get a).index = exchangeIndex (gaps d.gs).length 1 d.Θ.length a.index := by
  simp only [e,Route.get_index_cast,Route.exchange_get,swapBlocks_index,At.index_cast,
    List.length_cons,List.length_nil]

theorem square {A : NormalForm P} (a : At d.F A) :
    d.outer.route.get (d.t.get a) = d.e.get (d.inner.route.get a) := by
  apply At.index_injective
  rw [ContractionBlock.get_index,d.t_index,d.e_index,ContractionBlock.get_index]
  exact copyIndex_old d.C d.gs d.Θ a.index a.index_lt
theorem retained : d.e.get d.inner.keep = d.x := by
  apply At.index_injective
  rw [d.e_index,ContractionBlock.keep_index,d.x_index]
  change exchangeIndex (gaps d.gs).length 1 d.Θ.length (gaps d.gs).length =
    (gaps d.gs).length+d.Θ.length
  unfold exchangeIndex
  repeat first | split | omega
theorem inserted : d.outer.route.get d.z = d.x := by
  apply At.index_injective
  rw [ContractionBlock.get_index,d.z_index,d.x_index]
  exact copyIndex_last d.C d.gs d.Θ
theorem inserted_selected : d.z ∈ d.outer.selected := (d.outer.selected_iff _).mpr d.inserted

theorem t_injective {A : NormalForm P} (a b : At d.F A) (h : d.t.get a = d.t.get b) : a = b := by
  apply At.index_injective
  simpa only [d.t_index] using congrArg At.index h
theorem e_injective {A : NormalForm P} (a b : At d.I A) (h : d.e.get a = d.e.get b) : a = b := by
  apply At.index_injective
  have he := congrArg At.index h
  rw [d.e_index,d.e_index] at he
  have hh := congrArg (exchangeIndex (gaps d.gs).length d.Θ.length 1) he
  simpa only [GapExchange.exchange_inverse] using hh
theorem old_not_inserted {A : NormalForm P} (a : At d.F A) :
    (d.t.get a).index ≠ d.z.index := by
  rw [d.t_index,d.z_index]
  have he := a.index_lt
  omega

def back {A : NormalForm P} (a : At d.K A) : At d.I A :=
  ((a.cast d.exchangeTarget.symm).swapBlocks (gaps d.gs) d.Θ [d.C] []).cast d.exchangeSource
theorem back_index {A : NormalForm P} (a : At d.K A) :
    (d.back a).index = exchangeIndex (gaps d.gs).length d.Θ.length 1 a.index := by
  simp only [back,At.index_cast,swapBlocks_index,List.length_cons,List.length_nil]
theorem e_back {A : NormalForm P} (a : At d.K A) : d.e.get (d.back a) = a := by
  apply At.index_injective
  rw [d.e_index,d.back_index,GapExchange.exchange_inverse]
theorem back_e {A : NormalForm P} (a : At d.I A) : d.back (d.e.get a) = a := by
  apply At.index_injective
  rw [d.back_index,d.e_index,GapExchange.exchange_inverse]

end Data
end DosenPetric.Reduced.Gentzen.SelectedThinning
