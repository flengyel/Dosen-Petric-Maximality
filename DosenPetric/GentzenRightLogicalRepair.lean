module

public import DosenPetric.GentzenReducibilityLogical

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.W4.HeadRight
universe u
variable {P : Type u}
variable (d : Gentzen.SelectedLogical.Data P .disj)

theorem moveSource : []++d.s.I++[d.A,d.B]++[] = d.I := List.append_nil _
theorem moveTarget : []++[d.A,d.B]++d.s.I++[] = d.A::d.B::d.s.I := by
  simp only [List.nil_append,List.append_nil,List.cons_append]

def moveRoute : Route (d.A::d.B::d.s.I) d.I :=
  (Route.exchange [] d.s.I [d.A,d.B] []).cast (moveTarget d) (moveSource d)

theorem blockSource : repeated d.C [[],gaps d.gs]++d.Θ = d.C::d.s.I := by
  simp only [repeated,List.nil_append,List.append_assoc,List.cons_append]
theorem blockTarget : gaps [[],gaps d.gs]++d.C::d.Θ = d.s.I := by
  simp only [gaps,List.nil_append,List.append_nil]

abbrev block : ContractionBlock P (d.C::d.s.I) d.s.I :=
  ⟨d.C,[[],gaps d.gs],d.Θ,(blockSource d),(blockTarget d)⟩

def movedR (hn : 2 ≤ d.gs.length) (Γ : List (NormalForm P)) (f : G P Γ d.F) :
    G P Γ (d.A::d.B::d.s.I) :=
  UnaryCast.exchangeR [] d.s.I [d.A,d.B] [] (moveSource d) (moveTarget d) Γ
    (W4.SelectedLogical.innerR d hn Γ f)
def headR (hn : 2 ≤ d.gs.length) (Γ : List (NormalForm P)) (f : G P Γ d.F) :
    G P Γ (d.C::d.s.I) := G.disjR Γ [] d.s.I d.A d.B (movedR d hn Γ f)
def blockedR (hn : 2 ≤ d.gs.length) (Γ : List (NormalForm P)) (f : G P Γ d.F) :
    G P Γ d.s.I := (block d).applyR (Nat.le_refl 2) Γ (headR d hn Γ f)
def repairR (hn : 2 ≤ d.gs.length) (Γ : List (NormalForm P)) (f : G P Γ d.F) :
    G P Γ d.K := UnaryCast.exchangeR (gaps d.gs) [d.C] d.Θ []
      d.s.exchangeSource d.s.exchangeTarget Γ (blockedR d hn Γ f)

theorem blocked (hn : 2 ≤ d.gs.length) (Γ : List (NormalForm P)) (f : G P Γ d.F) :
    BlockedR (blockedR d hn Γ f) := by
  have h := BlockedR.disjunction d.A d.B Γ (gaps d.gs) d.Θ (movedR d hn Γ f)
  simpa only [blockedR,headR,ContractionBlock.applyR,BlockedSource.right2,G.reindex_trans]
    using h.reindex rfl (blockTarget d)

theorem count (hn : 2 ≤ d.gs.length) (Γ : List (NormalForm P)) (f : G P Γ d.F) :
    (repairR d hn Γ f).cutCount = f.cutCount := by
  simp only [repairR,blockedR,headR,movedR,UnaryCast.exchangeR,ContractionBlock.applyR,
    G.count_reindex,G.cutCount,W4.SelectedLogical.innerR]

theorem cutFree (hn : 2 ≤ d.gs.length) (Γ : List (NormalForm P)) (f : G P Γ d.F) :
    (repairR d hn Γ f).CutFree ↔ f.CutFree := by rw [G.CutFree,count]; rfl

theorem atomized (hn : 2 ≤ d.gs.length) (Γ : List (NormalForm P)) (f : G P Γ d.F) :
    (repairR d hn Γ f).Atomized ↔ f.Atomized := by
  simp only [repairR,blockedR,headR,movedR,UnaryCast.exchangeR,ContractionBlock.applyR,
    G.atomized_reindex,G.Atomized,W4.SelectedLogical.innerR]

theorem block_keep : (block d).keep = d.s.inner.keep := by
  apply At.index_injective
  simp only [ContractionBlock.keep_index,gaps,List.nil_append,List.append_nil]

theorem block_tail {E : NormalForm P} (a : At d.s.I E) : (block d).route.get a.there = a := by
  apply At.index_injective
  rw [ContractionBlock.get_index]
  change copyIndex [[],gaps d.gs] (a.index+1) = a.index
  simp only [copyIndex,gaps,List.length_nil,Nat.not_lt_zero,ite_false]
  repeat first | split | omega

theorem block_fresh : (block d).route.get (.here d.C d.s.I) = d.s.inner.keep := by
  apply At.index_injective
  rw [ContractionBlock.get_index,ContractionBlock.keep_index]
  simp only [At.index,copyIndex,gaps,List.length_nil,Nat.lt_irrefl,ite_false,ite_true,
    List.append_nil,Nat.zero_add]

theorem block_selected : (block d).selected = [.here d.C d.s.I,d.s.inner.keep.there] := by
  apply At.list_index_injective
  rw [(block d).selected_indices]
  simp only [copyOffsets,List.map_cons,List.map_nil,List.length_nil,Nat.zero_add,
    At.index,ContractionBlock.keep_index]
  simp only [Nat.add_comm]

theorem moved_index {E : NormalForm P} (a : At d.I E) :
    ((moveRoute d).get a).index = exchangeIndex 0 d.s.I.length 2 a.index := by
  simp only [moveRoute,Route.get_index_cast,Route.exchange_get,swapBlocks_index,
    At.index_cast,List.length_nil,List.length_cons]

theorem move_prefix {E : NormalForm P} (a : At d.s.I E) :
    (moveRoute d).get (a.before [d.A,d.B]) = At.shift [d.A,d.B] a := by
  apply At.index_injective
  rw [moved_index,At.index_before,At.index_shift]
  simp only [List.length_cons,List.length_nil]
  have hi := a.index_lt
  unfold exchangeIndex
  repeat first | split | omega

theorem move_first : (moveRoute d).get d.aI = .here d.A (d.B::d.s.I) := by
  apply At.index_injective
  rw [moved_index]
  simp only [Gentzen.SelectedLogical.Data.aI,At.index_shift,At.index,Nat.add_zero]
  unfold exchangeIndex
  repeat first | split | omega

theorem move_second : (moveRoute d).get d.bI = .there (.here d.B d.s.I) := by
  apply At.index_injective
  rw [moved_index]
  simp only [Gentzen.SelectedLogical.Data.bI,At.index_shift,At.index]
  unfold exchangeIndex
  repeat first | split | omega

end DosenPetric.Reduced.Gentzen.W4.HeadRight
