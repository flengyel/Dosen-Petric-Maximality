module

public import DosenPetric.GentzenTerminalContractionData

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.TerminalContraction
universe u
variable {P : Type u}
open Disjoint

/-- Copies before a terminal block commute with every bounded or unbounded block map. -/
theorem copy_splice_tail (C : NormalForm P) (gs : List (List (NormalForm P)))
    (u r s : Nat) (f : Nat → Nat) (i : Nat) :
    copyIndex gs (splice ((repeated C gs).length+u) r s f i) =
      splice ((gaps gs).length+1+u) r s f (copyIndex gs i) := by
  induction gs generalizing i with
  | nil =>
    simp only [repeated,gaps,List.length_nil,Nat.zero_add,copyIndex]
    have h := splice_add 1 u r s f i
    simpa only [Nat.add_comm] using h.symm
  | cons Γ gs ih =>
    simp only [repeated,gaps,List.length_append,List.length_cons]
    by_cases hi : i < Γ.length
    · rw [splice_before _ _ _ _ _ (by omega),copyIndex,ite_eq_left hi,
        splice_before _ _ _ _ _ (by omega)]
    · by_cases he : i = Γ.length
      · subst i
        rw [splice_before _ _ _ _ _ (by omega),copyIndex,
          ite_eq_right (Nat.lt_irrefl _),ite_eq_left rfl,splice_before _ _ _ _ _ (by omega)]
      · have hi' : i = Γ.length+1+(i-Γ.length-1) := by omega
        have hc : Γ.length+((repeated C gs).length+1)+u = (Γ.length+1)+((repeated C gs).length+u) := by omega
        have hl : Γ.length+(gaps gs).length+1+u = Γ.length+((gaps gs).length+1+u) := by omega
        rw [hc,hi',splice_add,GapLogical.copy_after,ih,GapLogical.copy_after,hl,splice_add]

namespace Data
variable (d : Data P)

theorem e0_index {A : NormalForm P} (a : At d.F A) :
    (d.e0.get a).index = splice d.upBefore.length (repeated d.E d.es).length
      ((gaps d.es).length+1) (copyIndex d.es) a.index := by
  rw [ContractionBlock.get_index]
  exact copy_splice d.E d.upBefore d.H d.hs a.index

theorem e1_index {A : NormalForm P} (a : At d.FC A) :
    (d.e1.get a).index = splice d.loBefore.length (repeated d.E d.es).length
      ((gaps d.es).length+1) (copyIndex d.es) a.index := by
  rw [ContractionBlock.get_index]
  exact copy_splice d.E d.loBefore d.H d.hs a.index

theorem square {A : NormalForm P} (a : At d.F A) : d.c1.get (d.e0.get a) = d.e1.get (d.c0.get a) := by
  apply At.index_injective
  rw [ContractionBlock.get_index,d.e0_index,d.e1_index,ContractionBlock.get_index]
  have h := copy_splice_tail d.C d.gs d.U.length (repeated d.E d.es).length
    ((gaps d.es).length+1) (copyIndex d.es) a.index
  have he : (gaps d.gs).length+1+d.U.length = (gaps d.gs).length+(d.U.length+1) := by omega
  simpa only [upBefore,loBefore,List.length_append,List.length_cons,he] using h

theorem e1_keepC0 : d.e1.get d.keepC0 = d.xC := by
  apply At.index_injective
  rw [d.e1_index,splice_before _ _ _ _ _ (by rw [d.keepC0_index]; simp only [loBefore,List.length_append,List.length_cons]; omega),
    d.keepC0_index,d.xC_index]

theorem c1_keepE0 : d.c1.get d.keepE0 = d.xE := by
  apply At.index_injective
  rw [ContractionBlock.get_index]
  rw [copy_tail d.C d.gs d.keepE0.index (by rw [d.keepE0_index]; simp only [upBefore,List.length_append]; omega)]
  rw [d.keepE0_index,d.xE_index]
  simp only [upBefore,List.length_append]
  omega

theorem product_square : comp (ofTerm d.c1.product) (ofTerm d.e0.product) = comp (ofTerm d.e1.product) (ofTerm d.c0.product) :=
  d.frame.product_square d.square

theorem coproduct_square : comp (ofTerm d.e0.coproduct) (ofTerm d.c1.coproduct) = comp (ofTerm d.c0.coproduct) (ofTerm d.e1.coproduct) :=
  d.frame.coproduct_square d.square

theorem selectedC_before (a : At d.F d.C) (ha : a ∈ d.selectedC0) : a.index < (repeated d.C d.gs).length := by
  have hi : a.index ∈ copyOffsets d.gs := by
    rw [← d.frame.bc0.selected_indices]; exact List.mem_map.mpr ⟨a,ha,rfl⟩
  exact GapExchange.selected_lt_repeated d.C d.gs a.index hi

theorem selectedE_inside (a : At d.F d.E) (ha : a ∈ d.selectedE0) :
    d.upBefore.length ≤ a.index ∧ a.index < d.upBefore.length+(repeated d.E d.es).length := by
  have hi : a.index ∈ copyOffsets d.eUpper := by
    rw [← d.frame.be0.selected_indices]; exact List.mem_map.mpr ⟨a,ha,rfl⟩
  rw [Disjoint.offsets_prefix] at hi
  obtain ⟨j,hj,he⟩ := List.mem_map.mp hi
  have h := GapExchange.selected_lt_repeated d.E d.es j hj
  omega

theorem selectedC1_before (a : At d.FE d.C) (ha : a ∈ d.selectedC1) : a.index < (repeated d.C d.gs).length := by
  have hi : a.index ∈ copyOffsets d.gs := by
    rw [← d.frame.bc1.selected_indices]; exact List.mem_map.mpr ⟨a,ha,rfl⟩
  exact GapExchange.selected_lt_repeated d.C d.gs a.index hi

theorem selectedE1_inside (a : At d.FC d.E) (ha : a ∈ d.selectedE1) :
    d.loBefore.length ≤ a.index ∧ a.index < d.loBefore.length+(repeated d.E d.es).length := by
  have hi : a.index ∈ copyOffsets d.eLower := by
    rw [← d.frame.be1.selected_indices]; exact List.mem_map.mpr ⟨a,ha,rfl⟩
  rw [Disjoint.offsets_prefix] at hi
  obtain ⟨j,hj,he⟩ := List.mem_map.mp hi
  have h := GapExchange.selected_lt_repeated d.E d.es j hj
  omega

theorem selected_separated (a : At d.F d.C) (b : At d.F d.E)
    (ha : a ∈ d.selectedC0) (hb : b ∈ d.selectedE0) : a.index < b.index := by
  have h := d.selectedC_before a ha
  have h' := d.selectedE_inside b hb
  simp only [upBefore,List.length_append] at h'
  omega

theorem selectedC_transport : d.selectedC1 = d.selectedC0.map d.e0.get :=
  d.frame.selectedC_transport d.square d.e1_keepC0 d.c1_keepE0 d.retained_distinct

theorem selectedE_transport : d.selectedE1 = d.selectedE0.map d.c0.get :=
  d.frame.selectedE_transport d.square d.e1_keepC0 d.c1_keepE0 d.retained_distinct

theorem selectedC0_length : d.selectedC0.length = d.gs.length := d.frame.selectedC0_length
theorem selectedC1_length : d.selectedC1.length = d.gs.length := d.frame.selectedC1_length
theorem selectedE0_length : d.selectedE0.length = d.es.length := d.frame.selectedE0_length
theorem selectedE1_length : d.selectedE1.length = d.es.length := d.frame.selectedE1_length

theorem selectedC_singleton (a : At d.F d.C) (ha : a ∈ d.selectedC0) :
    (TraceRoute.full d.e0).fiber (d.e0.get a) = [a] :=
  d.frame.selectedC_singleton d.square d.e1_keepC0 d.c1_keepE0 d.retained_distinct a ha

theorem selectedE_singleton (a : At d.F d.E) (ha : a ∈ d.selectedE0) :
    (TraceRoute.full d.c0).fiber (d.c0.get a) = [a] :=
  d.frame.selectedE_singleton d.square d.e1_keepC0 d.c1_keepE0 d.retained_distinct a ha

theorem xC_fiber : (TraceRoute.full d.e1).fiber d.xC = [d.keepC0] :=
  d.frame.xC_fiber d.e1_keepC0 d.retained_distinct

theorem xE_fiber : (TraceRoute.full d.c1).fiber d.xE = [d.keepE0] :=
  d.frame.xE_fiber d.c1_keepE0 d.retained_distinct

theorem selectedC_parametric (a : At d.F d.C) (ha : a ∈ d.selectedC0) :
    (d.e0.get a).index ≠ d.keepE0.index :=
  d.frame.selectedC0_parametric d.square d.e1_keepC0 d.c1_keepE0 d.retained_distinct a ha

theorem selectedE_parametric (a : At d.F d.E) (ha : a ∈ d.selectedE0) :
    (d.c0.get a).index ≠ d.keepC0.index :=
  d.frame.selectedE0_parametric d.square d.e1_keepC0 d.c1_keepE0 d.retained_distinct a ha

theorem selectedC_final (a : At d.F d.C) (ha : a ∈ d.selectedC0) :
    d.c1.get (d.e0.get a) = d.xC ∧ d.e1.get (d.c0.get a) = d.xC :=
  d.frame.selectedC_final d.square d.e1_keepC0 d.retained_distinct a ha

theorem selectedE_final (a : At d.F d.E) (ha : a ∈ d.selectedE0) :
    d.c1.get (d.e0.get a) = d.xE ∧ d.e1.get (d.c0.get a) = d.xE :=
  d.frame.selectedE_final d.square d.c1_keepE0 d.retained_distinct a ha

abbrev original {A : NormalForm P} (z : At d.K A) (hc : z.index ≠ d.xC.index)
    (he : z.index ≠ d.xE.index) : At d.F A := d.frame.originalViaE d.c1_keepE0 z hc he

theorem original_agree {A : NormalForm P} (z : At d.K A) (hc : z.index ≠ d.xC.index)
    (he : z.index ≠ d.xE.index) : d.frame.originalViaC d.e1_keepC0 z hc he = d.original z hc he :=
  d.frame.original_agree d.square d.e1_keepC0 d.c1_keepE0 z hc he

theorem other_fiber {A : NormalForm P} (z : At d.K A) (hc : z.index ≠ d.xC.index)
    (he : z.index ≠ d.xE.index) :
    (TraceRoute.full (d.e0.map d.c1.get)).fiber z = [d.original z hc he] ∧
    (TraceRoute.full (d.c0.map d.e1.get)).fiber z = [d.original z hc he] :=
  d.frame.other_fiber d.square d.e1_keepC0 d.c1_keepE0 z hc he

end Data
end DosenPetric.Reduced.Gentzen.TerminalContraction
