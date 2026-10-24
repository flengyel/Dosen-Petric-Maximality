module

public import DosenPetric.GentzenDisjointRanks

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

/-- On fixed positions only, deletion of selected copies preserves order. -/
theorem copyIndex_strict_fixed (gs : List (List (NormalForm P))) (i j : Nat)
    (hi : copyIndex gs i ≠ (gaps gs).length) (hj : copyIndex gs j ≠ (gaps gs).length)
    (hij : i < j) : copyIndex gs i < copyIndex gs j := by
  induction gs generalizing i j with
  | nil => simp only [copyIndex]; omega
  | cons Γ gs ih =>
    simp only [gaps,List.length_append] at hi hj
    by_cases hp : i < Γ.length
    · rw [copyIndex,ite_eq_left hp]
      rw [copyIndex] at hj ⊢
      split
      · exact hij
      · split
        · omega
        · omega
    · by_cases he : i = Γ.length
      · simp only [copyIndex,ite_eq_right hp,ite_eq_left he] at hi
        omega
      · have jp : ¬ j < Γ.length := by omega
        have je : j ≠ Γ.length := by omega
        simp only [copyIndex,ite_eq_right hp,ite_eq_right he,ite_eq_right jp,ite_eq_right je] at hi hj ⊢
        have h := ih (i-Γ.length-1) (j-Γ.length-1) (by omega) (by omega) (by omega)
        omega

namespace ContractionBlock
variable {U K : List (NormalForm P)} (b : ContractionBlock P U K)
theorem get_strict_fixed {A B : NormalForm P} (a : At U A) (c : At U B)
    (ha : (b.route.get a).index ≠ b.keep.index) (hc : (b.route.get c).index ≠ b.keep.index)
    (h : a.index < c.index) : (b.route.get a).index < (b.route.get c).index := by
  simp only [b.get_index,b.keep_index] at ha hc ⊢
  exact copyIndex_strict_fixed b.gs a.index c.index ha hc h
end ContractionBlock

/-- Raw contraction coordinates and endpoint identifications only.
No routing square, equality of arrows, or rank law is stored here. -/
structure ContractionFrame (P : Type u) where
  C : NormalForm P
  E : NormalForm P
  cgs0 : List (List (NormalForm P))
  cgs1 : List (List (NormalForm P))
  egs0 : List (List (NormalForm P))
  egs1 : List (List (NormalForm P))
  ct0 : List (NormalForm P)
  ct1 : List (NormalForm P)
  et0 : List (NormalForm P)
  et1 : List (NormalForm P)
  F : List (NormalForm P)
  FE : List (NormalForm P)
  FC : List (NormalForm P)
  K : List (NormalForm P)
  upperC0 : repeated C cgs0 ++ ct0 = F
  lowerC0 : gaps cgs0 ++ C :: ct0 = FC
  upperC1 : repeated C cgs1 ++ ct1 = FE
  lowerC1 : gaps cgs1 ++ C :: ct1 = K
  upperE0 : repeated E egs0 ++ et0 = F
  lowerE0 : gaps egs0 ++ E :: et0 = FE
  upperE1 : repeated E egs1 ++ et1 = FC
  lowerE1 : gaps egs1 ++ E :: et1 = K
  countC : cgs1.length = cgs0.length
  countE : egs1.length = egs0.length

namespace ContractionFrame
variable (d : ContractionFrame P)
abbrev bc0 : ContractionBlock P d.F d.FC := ⟨d.C,d.cgs0,d.ct0,d.upperC0,d.lowerC0⟩
abbrev bc1 : ContractionBlock P d.FE d.K := ⟨d.C,d.cgs1,d.ct1,d.upperC1,d.lowerC1⟩
abbrev be0 : ContractionBlock P d.F d.FE := ⟨d.E,d.egs0,d.et0,d.upperE0,d.lowerE0⟩
abbrev be1 : ContractionBlock P d.FC d.K := ⟨d.E,d.egs1,d.et1,d.upperE1,d.lowerE1⟩
abbrev c0 := d.bc0.route
abbrev c1 := d.bc1.route
abbrev e0 := d.be0.route
abbrev e1 := d.be1.route
abbrev selectedC0 := d.bc0.selected
abbrev selectedC1 := d.bc1.selected
abbrev selectedE0 := d.be0.selected
abbrev selectedE1 := d.be1.selected
abbrev keepC0 := d.bc0.keep
abbrev keepE0 := d.be0.keep
abbrev xC := d.bc1.keep
abbrev xE := d.be1.keep

theorem selectedC0_length : d.selectedC0.length = d.cgs0.length := d.bc0.selected_length
theorem selectedC1_length : d.selectedC1.length = d.cgs0.length := d.bc1.selected_length.trans d.countC
theorem selectedE0_length : d.selectedE0.length = d.egs0.length := d.be0.selected_length
theorem selectedE1_length : d.selectedE1.length = d.egs0.length := d.be1.selected_length.trans d.countE

variable (hSq : ∀ {A : NormalForm P} (a : At d.F A), d.c1.get (d.e0.get a) = d.e1.get (d.c0.get a))
variable (hC : d.e1.get d.keepC0 = d.xC) (hE : d.c1.get d.keepE0 = d.xE)
variable (hSep : d.xC.index ≠ d.xE.index)

include hSq in
theorem product_square : comp (ofTerm d.c1.product) (ofTerm d.e0.product) = comp (ofTerm d.e1.product) (ofTerm d.c0.product) := by
  apply product_positions
  intro A a
  rw [Laws.assoc,Route.product_get,Route.product_get,Laws.assoc,Route.product_get,Route.product_get]
  exact congrArg (fun x => ofTerm x.projection) (hSq a)

include hSq in
theorem coproduct_square : comp (ofTerm d.e0.coproduct) (ofTerm d.c1.coproduct) = comp (ofTerm d.c0.coproduct) (ofTerm d.e1.coproduct) := by
  apply coproduct_positions
  intro A a
  rw [← Laws.assoc,Route.coproduct_get,Route.coproduct_get,← Laws.assoc,Route.coproduct_get,Route.coproduct_get]
  exact congrArg (fun x => ofTerm x.injection) (hSq a)

include hSq hC hE hSep in
theorem selectedC0_parametric (a : At d.F d.C) (ha : a ∈ d.selectedC0) : (d.e0.get a).index ≠ d.keepE0.index := by
  have h₀ := (d.bc0.selected_iff a).mp ha
  have h₁ := congrArg At.index ((hSq a).trans ((congrArg d.e1.get h₀).trans hC))
  have h₂ := congrArg At.index hE
  rw [ContractionBlock.get_index] at h₁ h₂
  intro hi
  rw [hi,h₂] at h₁
  exact hSep h₁.symm

include hSq hC hE hSep in
theorem selectedE0_parametric (a : At d.F d.E) (ha : a ∈ d.selectedE0) : (d.c0.get a).index ≠ d.keepC0.index := by
  have h₀ := (d.be0.selected_iff a).mp ha
  have h₁ := congrArg At.index ((hSq a).symm.trans ((congrArg d.c1.get h₀).trans hE))
  have h₂ := congrArg At.index hC
  rw [ContractionBlock.get_index] at h₁ h₂
  intro hi
  rw [hi,h₂] at h₁
  exact hSep h₁

include hE hSep in
theorem selectedC1_fixed (a : At d.FE d.C) (ha : a ∈ d.selectedC1) : a.index ≠ d.keepE0.index := by
  have h₁ := congrArg At.index ((d.bc1.selected_iff a).mp ha)
  have h₂ := congrArg At.index hE
  rw [ContractionBlock.get_index] at h₁ h₂
  intro hi
  rw [hi,h₂] at h₁
  exact hSep h₁.symm

include hC hSep in
theorem selectedE1_fixed (a : At d.FC d.E) (ha : a ∈ d.selectedE1) : a.index ≠ d.keepC0.index := by
  have h₁ := congrArg At.index ((d.be1.selected_iff a).mp ha)
  have h₂ := congrArg At.index hC
  rw [ContractionBlock.get_index] at h₁ h₂
  intro hi
  rw [hi,h₂] at h₁
  exact hSep h₁

end ContractionFrame
end DosenPetric.Reduced.Gentzen
