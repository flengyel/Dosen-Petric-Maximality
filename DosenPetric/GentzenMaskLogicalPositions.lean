module

public import DosenPetric.GentzenMaskContextCoordinates

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.SelectionMask
universe u
variable {P : Type u} {C : NormalForm P} {Γ Θ : List (NormalForm P)}
variable (g : SelectionMask C Γ) (t : SelectionMask C Θ) (A B D : NormalForm P)

theorem context_parent {E : NormalForm P} (a : At (Γ++A::B::Θ) E) :
    (At.fixed Γ [A,B] [D] Θ a).map (contextCanonical g t [D]).get=
      At.fixed (C::g.erased) [A,B] [D] t.erased ((contextCanonical g t [A,B]).get a) := by
  cases At.cases_append Γ ([A,B]++Θ) a with
  | inl h=>
    obtain ⟨a,rfl⟩:=h
    apply At.option_index_injective
    rw [At.fixed_before,Option.map_some,Option.map_some]
    apply Eq.trans ?_ (At.fixed_index (C::g.erased) [A,B] [D] t.erased
      ((contextCanonical g t [A,B]).get (a.before ([A,B]++Θ)))).symm
    rw [contextCanonical_before,contextCanonical_before]
    simp only [List.length_cons,List.length_cons,List.length_nil]
    have hh:=g.offset_lt a
    cases hp : g.picked a <;> simp only [Bool.false_eq_true,ite_false,ite_true]
    · have hl:=hh hp
      unfold GapLogical.parentIndex
      exact (ite_eq_left (by omega)).symm
    · unfold GapLogical.parentIndex
      exact (ite_eq_left (by omega)).symm
  | inr h=>
    obtain ⟨a,rfl⟩:=h
    cases At.cases_append [A,B] Θ a with
    | inl h=>
      obtain ⟨a,rfl⟩:=h
      have ha:=a.index_lt
      apply At.option_index_injective
      rw [At.fixed_middle,Option.map_none,Option.map_none]
      apply Eq.trans ?_ (At.fixed_index (C::g.erased) [A,B] [D] t.erased
        ((contextCanonical g t [A,B]).get (At.shift Γ (a.before Θ)))).symm
      rw [contextCanonical_middle]
      simp only [List.length_cons,List.length_nil] at ha ⊢
      unfold GapLogical.parentIndex
      rw [ite_eq_right (by omega),ite_eq_left (by omega)]
    | inr h=>
      obtain ⟨a,rfl⟩:=h
      apply At.option_index_injective
      rw [At.fixed_tail,Option.map_some,Option.map_some]
      apply Eq.trans ?_ (At.fixed_index (C::g.erased) [A,B] [D] t.erased
        ((contextCanonical g t [A,B]).get (At.shift Γ (At.shift [A,B] a)))).symm
      rw [contextCanonical_tail,contextCanonical_tail]
      simp only [List.length_cons,List.length_nil]
      cases hp : t.picked a <;> simp only [Bool.false_eq_true,ite_false,ite_true]
      · unfold GapLogical.parentIndex
        rw [ite_eq_right (by omega),ite_eq_right (by omega)]
        congr 1
        omega
      · unfold GapLogical.parentIndex
        exact (ite_eq_left (by omega)).symm

theorem context_middle {E : NormalForm P} (M : List (NormalForm P)) (a : At M E) :
    (contextCanonical g t M).get (At.shift Γ (a.before Θ))=
      At.shift (C::g.erased) (a.before t.erased) := by
  apply At.index_injective
  rw [contextCanonical_middle,At.index_shift,At.index_before]
  simp only [List.length_cons]
  omega
end DosenPetric.Reduced.Gentzen.SelectionMask
