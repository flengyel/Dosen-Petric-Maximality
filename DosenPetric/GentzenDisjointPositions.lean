module

public import DosenPetric.GentzenDisjointData

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.Disjoint
universe u
variable {P : Type u}

theorem copy_inside (C : NormalForm P) (pre post : List (List (NormalForm P)))
    (U X V : List (NormalForm P)) (j : Nat) (hj : j < X.length) :
    copyIndex (pre++(U++(X++V))::post) ((repeated C pre++U).length+j) = (gaps pre++U).length+j := by
  induction pre with
  | nil =>
    simp only [List.nil_append,repeated,List.nil_append]
    rw [copyIndex,ite_eq_left (by simp only [List.length_append]; omega)]
  | cons Γ pre ih =>
    simp only [List.cons_append,repeated,gaps,List.length_append,List.length_cons] at *
    have he : Γ.length+((repeated C pre).length+1)+U.length+j = Γ.length+1+((repeated C pre).length+U.length+j) := by omega
    rw [he,GapLogical.copy_after,ih]
    omega

theorem offsets_prefix (W H : List (NormalForm P)) (hs : List (List (NormalForm P))) :
    copyOffsets ((W++H)::hs) = (copyOffsets (H::hs)).map (fun i => W.length+i) := by
  simp only [copyOffsets,List.length_append,List.map_cons,List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_def]
  omega

theorem splice_outside_strict (k r s : Nat) (f : Nat → Nat) (i j : Nat)
    (hi : i < k ∨ k+r ≤ i) (hj : j < k ∨ k+r ≤ j) (h : i < j) :
    splice k r s f i < splice k r s f j := by
  rcases hi with hi | hi <;> rcases hj with hj | hj
  · rw [splice_before _ _ _ _ _ hi,splice_before _ _ _ _ _ hj]; exact h
  · rw [splice_before _ _ _ _ _ hi,splice_after _ _ _ _ _ hj]; omega
  · omega
  · rw [splice_after _ _ _ _ _ hi,splice_after _ _ _ _ _ hj]; omega

namespace Data
variable (d : Data P)

theorem selectedC0_outside (a : At d.F d.C) (ha : a ∈ d.selectedC0) :
    a.index < d.upBefore.length ∨ d.upBefore.length+(repeated d.E d.es).length ≤ a.index := by
  have hm : a.index ∈ copyOffsets d.outer0 := by
    rw [← d.bc0.selected_indices]; exact List.mem_map.mpr ⟨a,ha,rfl⟩
  exact GapLogical.selected_outside d.C d.pre d.post d.U (repeated d.E d.es) d.V a.index hm

theorem selectedC1_outside (a : At d.FE d.C) (ha : a ∈ d.selectedC1) :
    a.index < d.upBefore.length ∨ d.upBefore.length+(gaps d.es).length+1 ≤ a.index := by
  have hm : a.index ∈ copyOffsets d.outer1 := by
    rw [← d.bc1.selected_indices]; exact List.mem_map.mpr ⟨a,ha,rfl⟩
  have h := GapLogical.selected_outside d.C d.pre d.post d.U (gaps d.es++[d.E]) d.V a.index
    (by simpa only [outer1,List.append_assoc,List.singleton_append] using hm)
  simpa only [List.length_append,List.length_singleton,Nat.add_assoc] using h

theorem selectedE0_inside (a : At d.F d.E) (ha : a ∈ d.selectedE0) :
    d.upBefore.length ≤ a.index ∧ a.index < d.upBefore.length+(repeated d.E d.es).length := by
  have hm : a.index ∈ copyOffsets d.eUpper := by
    rw [← d.be0.selected_indices]; exact List.mem_map.mpr ⟨a,ha,rfl⟩
  rw [offsets_prefix] at hm
  obtain ⟨j,hj,he⟩ := List.mem_map.mp hm
  have hh := GapExchange.selected_lt_repeated d.E d.es j hj
  omega

theorem selectedE1_inside (a : At d.FC d.E) (ha : a ∈ d.selectedE1) :
    d.loBefore.length ≤ a.index ∧ a.index < d.loBefore.length+(repeated d.E d.es).length := by
  have hm : a.index ∈ copyOffsets d.eLower := by
    rw [← d.be1.selected_indices]; exact List.mem_map.mpr ⟨a,ha,rfl⟩
  rw [offsets_prefix] at hm
  obtain ⟨j,hj,he⟩ := List.mem_map.mp hm
  have hh := GapExchange.selected_lt_repeated d.E d.es j hj
  omega

theorem c0_inside {A : NormalForm P} (a : At d.F A)
    (ha : d.upBefore.length ≤ a.index) (hb : a.index < d.upBefore.length+(repeated d.E d.es).length) :
    (d.c0.get a).index = d.loBefore.length+(a.index-d.upBefore.length) := by
  rw [ContractionBlock.get_index]
  have h := copy_inside d.C d.pre d.post d.U (repeated d.E d.es) d.V
    (a.index-d.upBefore.length) (by omega)
  have he : a.index = d.upBefore.length+(a.index-d.upBefore.length) := by omega
  rw [← he] at h
  exact h

theorem c1_inside {A : NormalForm P} (a : At d.FE A)
    (ha : d.upBefore.length ≤ a.index) (hb : a.index < d.upBefore.length+(gaps d.es).length+1) :
    (d.c1.get a).index = d.loBefore.length+(a.index-d.upBefore.length) := by
  rw [ContractionBlock.get_index]
  have hl : (gaps d.es++[d.E]).length = (gaps d.es).length+1 := by rw [List.length_append]; rfl
  have hj : a.index-d.upBefore.length < (gaps d.es++[d.E]).length := by rw [hl]; omega
  have h := copy_inside d.C d.pre d.post d.U (gaps d.es++[d.E]) d.V
    (a.index-d.upBefore.length) hj
  have he : a.index = d.upBefore.length+(a.index-d.upBefore.length) := by omega
  rw [← he] at h
  simpa only [bc1,outer1,List.append_assoc,List.singleton_append] using h

theorem c1_keepE0 : d.c1.get d.keepE0 = d.xE := by
  apply At.index_injective
  rw [d.c1_inside _ (by rw [d.keepE0_index]; omega) (by rw [d.keepE0_index]; omega),d.keepE0_index,d.xE_index]
  omega

theorem e1_keepC0 : d.e1.get d.keepC0 = d.xC := by
  apply At.index_injective
  rw [d.e1_index,splice_after _ _ _ _ _ (by rw [d.keepC0_index]; omega),d.keepC0_index,d.xC_index,d.xE_index]
  omega

theorem selectedC0_parametric (a : At d.F d.C) (ha : a ∈ d.selectedC0) :
    (d.e0.get a).index ≠ d.keepE0.index := by
  have h := d.selectedC0_outside a ha
  rw [d.e0_index,d.keepE0_index]
  rcases h with h | h
  · rw [splice_before _ _ _ _ _ h]; omega
  · rw [splice_after _ _ _ _ _ h]; omega

theorem selectedE0_parametric (a : At d.F d.E) (ha : a ∈ d.selectedE0) :
    (d.c0.get a).index ≠ d.keepC0.index := by
  have h := d.selectedE0_inside a ha
  rw [d.c0_inside a h.1 h.2,d.keepC0_index]
  omega

theorem selectedC1_fixed (a : At d.FE d.C) (ha : a ∈ d.selectedC1) : a.index ≠ d.keepE0.index := by
  have h := d.selectedC1_outside a ha
  rw [d.keepE0_index]
  omega

theorem selectedE1_fixed (a : At d.FC d.E) (ha : a ∈ d.selectedE1) : a.index ≠ d.keepC0.index := by
  have h := d.selectedE1_inside a ha
  rw [d.keepC0_index]
  omega

end Data
end DosenPetric.Reduced.Gentzen.Disjoint
