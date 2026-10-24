module

public import DosenPetric.GentzenSelectedThinningFibers

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

namespace At
theorem list_index_injective {Γ : List (NormalForm P)} {A : NormalForm P}
    (xs ys : List (At Γ A)) (h : xs.map At.index = ys.map At.index) : xs = ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> cases h; rfl
  | cons a xs ih =>
    cases ys with
    | nil => cases h
    | cons b ys =>
      have he := List.cons.inj h
      cases At.index_injective a b he.1
      exact congrArg (List.cons a) (ih ys he.2)
end At

namespace ContractionBlock
variable {F K : List (NormalForm P)} (d : ContractionBlock P F K)
abbrev extend (Ξ : List (NormalForm P)) : ContractionBlock P (F++Ξ) (K++Ξ) where
  C := d.C
  gs := d.gs
  tail := d.tail++Ξ
  upper := by rw [← List.append_assoc,d.upper]
  lower := by rw [← List.cons_append,← List.append_assoc,d.lower]

theorem extend_before (Ξ : List (NormalForm P)) {A : NormalForm P} (a : At F A) :
    (d.extend Ξ).route.get (a.before Ξ) = (d.route.get a).before Ξ := by
  apply At.index_injective
  simp only [get_index,extend,At.index_before]

theorem extend_shift (Ξ : List (NormalForm P)) {A : NormalForm P} (a : At Ξ A) :
    (d.extend Ξ).route.get (At.shift F a) = At.shift K a := by
  apply At.index_injective
  rw [get_index,At.index_shift,At.index_shift]
  change copyIndex d.gs (F.length+a.index) = K.length+a.index
  have hu := congrArg List.length d.upper
  have hl := congrArg List.length d.lower
  simp only [List.length_append,List.length_cons] at hu hl
  rw [← hu]
  have he : (repeated d.C d.gs).length+d.tail.length+a.index =
      (repeated d.C d.gs).length+(d.tail.length+a.index) := by omega
  rw [he,GapInsertion.copyIndex_tail_inserted]
  omega

theorem extend_keep (Ξ : List (NormalForm P)) : (d.extend Ξ).keep = d.keep.before Ξ := by
  apply At.index_injective
  simp only [keep_index,extend,At.index_before]

theorem extend_selected (Ξ : List (NormalForm P)) :
    (d.extend Ξ).selected = d.selected.map (fun a => a.before Ξ) := by
  apply At.list_index_injective
  have he : (d.selected.map (fun a => a.before Ξ)).map At.index = d.selected.map At.index := by
    simp only [List.map_map,Function.comp_def,At.index_before]
  exact (d.extend Ξ).selected_indices.trans (d.selected_indices.symm.trans he.symm)
end ContractionBlock
end DosenPetric.Reduced.Gentzen
