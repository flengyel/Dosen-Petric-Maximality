module

public import DosenPetric.GentzenMaskCoordinates

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.SelectionMask
universe u
variable {P : Type u} {C : NormalForm P}
variable {Γ X Y Θ : List (NormalForm P)}

def quad (g : SelectionMask C Γ) (x : SelectionMask C X)
    (y : SelectionMask C Y) (t : SelectionMask C Θ) : SelectionMask C (Γ++X++Y++Θ) :=
  ((g.append x).append y).append t

theorem quad_count (g : SelectionMask C Γ) (x : SelectionMask C X)
    (y : SelectionMask C Y) (t : SelectionMask C Θ) :
    (quad g x y t).count=g.count+x.count+y.count+t.count := by
  simp only [quad,append_count]

theorem quad_erased (g : SelectionMask C Γ) (x : SelectionMask C X)
    (y : SelectionMask C Y) (t : SelectionMask C Θ) :
    (quad g x y t).erased=g.erased++x.erased++y.erased++t.erased := by
  simp only [quad,append_erased]

/-- Exchange the fixed slots, keeping the distinguished selected anchor at
position zero. This equation is on whole-formula positions. -/
theorem swap_canonical_index (g : SelectionMask C Γ) (x : SelectionMask C X)
    (y : SelectionMask C Y) (t : SelectionMask C Θ)
    {A : NormalForm P} (a : At (Γ++X++Y++Θ) A) :
    ((quad g y x t).canonical.get (a.swapBlocks Γ X Y Θ)).index=
      exchangeIndex (g.erased.length+1) x.erased.length y.erased.length
        ((quad g x y t).canonical.get a).index := by
  cases At.cases_append (Γ++X++Y) Θ a with
  | inr h=>
    obtain ⟨b,rfl⟩:=h
    simp only [At.swapBlocks,At.splitAppend_shift,canonical_index,quad,
      append_picked_shift,append_offset_shift,append_erased,List.length_append]
    cases hp : t.picked b <;> simp only [Bool.false_eq_true,ite_false,ite_true]
    · unfold exchangeIndex
      split <;> (try split) <;> (try split) <;> omega
    · unfold exchangeIndex
      exact (ite_eq_left (by omega)).symm
  | inl h=>
    obtain ⟨b,rfl⟩:=h
    cases At.cases_append (Γ++X) Y b with
    | inr h=>
      obtain ⟨c,rfl⟩:=h
      have hc:=y.offset_lt c
      simp only [At.swapBlocks,At.splitAppend_before,At.splitAppend_shift,canonical_index,quad,
        append_picked_before,append_picked_shift,append_offset_before,append_offset_shift,
        append_erased,List.length_append]
      cases hp : y.picked c <;> simp only [Bool.false_eq_true,ite_false,ite_true]
      · have hh:=hc hp
        unfold exchangeIndex
        split <;> (try split) <;> (try split) <;> omega
      · unfold exchangeIndex
        exact (ite_eq_left (by omega)).symm
    | inl h=>
      obtain ⟨c,rfl⟩:=h
      cases At.cases_append Γ X c with
      | inr h=>
        obtain ⟨d,rfl⟩:=h
        have hd:=x.offset_lt d
        simp only [At.swapBlocks,At.splitAppend_before,At.splitAppend_shift,canonical_index,quad,
          append_picked_before,append_picked_shift,append_offset_before,append_offset_shift,
          append_erased,List.length_append]
        cases hp : x.picked d <;> simp only [Bool.false_eq_true,ite_false,ite_true]
        · have hh:=hd hp
          unfold exchangeIndex
          split <;> (try split) <;> (try split) <;> omega
        · unfold exchangeIndex
          exact (ite_eq_left (by omega)).symm
      | inl h=>
        obtain ⟨d,rfl⟩:=h
        have hd:=g.offset_lt d
        simp only [At.swapBlocks,At.splitAppend_before,canonical_index,quad,
          append_picked_before,append_offset_before]
        cases hp : g.picked d <;> simp only [Bool.false_eq_true,ite_false,ite_true]
        · have hh:=hd hp
          unfold exchangeIndex
          exact (ite_eq_left (by omega)).symm
        · unfold exchangeIndex
          exact (ite_eq_left (by omega)).symm

end DosenPetric.Reduced.Gentzen.SelectionMask
