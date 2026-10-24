module

public import DosenPetric.GentzenContractionAppend

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.SelectedLogical
universe u
variable {P : Type u}

structure Data (P : Type u) (o : Op) where
  A : NormalForm P
  B : NormalForm P
  gs : List (List (NormalForm P))
  Θ : List (NormalForm P)

namespace Data
variable {o : Op} (d : Data P o)
abbrev C := o.formula d.A d.B
abbrev s : SelectedThinning.Data P := ⟨d.C,d.gs,d.Θ⟩
abbrev F := d.s.F++[d.A,d.B]
abbrev I := d.s.I++[d.A,d.B]
abbrev U := d.s.U
abbrev J := d.s.I++[d.C]
abbrev K := d.s.K
abbrev inner : ContractionBlock P d.F d.I := d.s.inner.extend [d.A,d.B]
abbrev outer : ContractionBlock P d.U d.K := d.s.outer

theorem lastSource : repeated d.C [gaps d.gs,d.Θ]++[] = d.J := by
  simp only [repeated,List.append_nil,List.append_assoc,List.cons_append]
theorem lastTarget : gaps [gaps d.gs,d.Θ]++d.C::[] = d.K := by
  simp only [gaps,List.append_nil]
abbrev last : ContractionBlock P d.J d.K :=
  ⟨d.C,[gaps d.gs,d.Θ],[],d.lastSource,d.lastTarget⟩
abbrev x := d.outer.keep
def q : At d.J d.C := At.shift d.s.I (.here d.C [])
def k : At d.J d.C := d.s.inner.keep.before [d.C]
def a : At d.F d.A := At.shift d.s.F (.here d.A [d.B])
def b : At d.F d.B := At.shift d.s.F (.there (.here d.B []))
def aI : At d.I d.A := At.shift d.s.I (.here d.A [d.B])
def bI : At d.I d.B := At.shift d.s.I (.there (.here d.B []))
def uParent {E : NormalForm P} (a : At d.F E) : Option (At d.U E) :=
  At.fixed d.s.F [d.A,d.B] [d.C] [] a
def iParent {E : NormalForm P} (a : At d.I E) : Option (At d.J E) :=
  At.fixed d.s.I [d.A,d.B] [d.C] [] a

theorem t_before {E : NormalForm P} (a : At d.s.F E) : d.s.t.get a = a.before [d.C] :=
  At.index_injective _ _ ((d.s.t_index a).trans (At.index_before a _).symm)
theorem last_keep : d.last.keep = d.x := by
  apply At.index_injective
  rw [ContractionBlock.keep_index,d.s.x_index]
  simp only [gaps,List.append_nil,List.length_append]
theorem last_prefix {E : NormalForm P} (a : At d.s.I E) :
    d.last.route.get (a.before [d.C]) = d.s.e.get a := by
  apply At.index_injective
  rw [ContractionBlock.get_index,At.index_before,d.s.e_index]
  change copyIndex [gaps d.gs,d.Θ] a.index =
    exchangeIndex (gaps d.gs).length 1 d.Θ.length a.index
  have hi := a.index_lt
  change a.index < (gaps d.gs++d.C::d.Θ).length at hi
  simp only [List.length_append,List.length_cons] at hi
  simp only [copyIndex,gaps,List.append_nil,List.length_nil,exchangeIndex]
  repeat first | split | omega
theorem last_principal : d.last.route.get d.q = d.x := by
  apply At.index_injective
  rw [ContractionBlock.get_index,d.s.x_index]
  simp only [q,At.index_shift,At.index,Nat.add_zero,List.length_append,List.length_cons]
  change copyIndex [gaps d.gs,d.Θ] ((gaps d.gs).length+(d.Θ.length+1)) =
    (gaps d.gs).length+d.Θ.length
  simp only [copyIndex,gaps,List.append_nil,List.length_nil]
  repeat first | split | omega
theorem last_retained : d.last.route.get d.k = d.x := by
  exact (d.last_prefix d.s.inner.keep).trans d.s.retained
theorem prefix_square {E : NormalForm P} (a : At d.s.F E) :
    d.outer.route.get (a.before [d.C]) =
      d.last.route.get ((d.s.inner.route.get a).before [d.C]) := by
  rw [← d.t_before,d.last_prefix]
  exact d.s.square a
theorem inner_a : d.inner.route.get d.a = d.aI := d.s.inner.extend_shift _ _
theorem inner_b : d.inner.route.get d.b = d.bI := d.s.inner.extend_shift _ _
theorem consumed_a : d.uParent d.a = none := At.fixed_middle _ _ _ _ (.here d.A [d.B])
theorem consumed_b : d.uParent d.b = none := At.fixed_middle _ _ _ _ (.there (.here d.B []))
theorem inner_consumed_a : d.iParent d.aI = none := At.fixed_middle _ _ _ _ (.here d.A [d.B])
theorem inner_consumed_b : d.iParent d.bI = none := At.fixed_middle _ _ _ _ (.there (.here d.B []))
theorem u_prefix {E : NormalForm P} (a : At d.s.F E) :
    d.uParent (a.before [d.A,d.B]) = some (a.before [d.C]) := At.fixed_before ..
theorem i_prefix {E : NormalForm P} (a : At d.s.I E) :
    d.iParent (a.before [d.A,d.B]) = some (a.before [d.C]) := At.fixed_before ..

theorem partial_square {E : NormalForm P} (a : At d.F E) :
    (d.uParent a).map d.outer.route.get =
      (d.iParent (d.inner.route.get a)).map d.last.route.get := by
  cases At.cases_append d.s.F [d.A,d.B] a with
  | inl h =>
    obtain ⟨a,rfl⟩ := h
    rw [d.u_prefix,ContractionBlock.extend_before,d.i_prefix,Option.map_some,Option.map_some,d.prefix_square]
  | inr h =>
    obtain ⟨a,rfl⟩ := h
    cases a with
    | here => rw [show At.shift d.s.F (.here d.A [d.B]) = d.a from rfl,d.inner_a,d.consumed_a,d.inner_consumed_a]; rfl
    | there a =>
      cases a with
      | here => rw [show At.shift d.s.F (.there (.here d.B [])) = d.b from rfl,d.inner_b,d.consumed_b,d.inner_consumed_b]; rfl
      | there a => cases a

theorem last_selected : d.last.selected = [d.k,d.q] := by
  apply At.list_index_injective
  exact d.last.selected_indices.trans (by
    simp only [List.map_cons,List.map_nil,k,q,At.index_before,ContractionBlock.keep_index,
      At.index_shift,At.index,Nat.add_zero,copyOffsets,List.length_append,List.length_cons,
      List.map_nil,List.map_cons]
    congr 2 <;> omega)
theorem inner_selected : d.inner.selected = d.s.inner.selected.map (fun a => a.before [d.A,d.B]) :=
  d.s.inner.extend_selected _
theorem outer_selected : d.outer.selected = d.s.inner.selected.map (fun a => a.before [d.C])++[d.s.z] := by
  exact d.s.selected_transport.trans (by rw [List.map_congr_left (fun a _ => d.t_before a)])
end Data
end DosenPetric.Reduced.Gentzen.SelectedLogical
