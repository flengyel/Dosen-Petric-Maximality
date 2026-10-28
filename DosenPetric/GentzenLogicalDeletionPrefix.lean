module

public import DosenPetric.GentzenErasureContexts

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace LogicalDeletion

/-- Delete a nonprincipal prefix tag through either native unary logical comparison. -/
theorem before_square (o : Op) {F : List (NormalForm P)} (U : List (NormalForm P))
    (A B : NormalForm P) {C : NormalForm P} (a : At F C) :
    (side P o).comp ((headBefore a (o.formula A B :: U)).arrow o) (logicalSide o F U A B) =
      (side P o).comp
        ((sideM P o).tensor ((side P o).id C) (logicalSide o a.erase U A B))
        ((headBefore a (A :: B :: U)).arrow o) := by
  let S := side P o
  let M := sideM P o
  let D := sideD P o
  apply side_ext o
  intro E b
  rw [S.assoc,S.assoc,ExchangeScript.component]
  cases At.cases_append F (A :: B :: U) b with
  | inl hb =>
    obtain ⟨b,rfl⟩ := hb
    rw [logical_prefix,ExchangeScript.component]
    by_cases hi : b.index = a.index
    · have he := b.formula_eq a hi
      cases he
      have he : b = a := by apply At.index_injective; exact hi
      cases he
      rw [headBefore_selected,headBefore_selected,component_here,component_here,← D.fst_nat,S.comp_id]
    · obtain ⟨b,rfl⟩ : ∃ b' : At a.erase E, b = a.retain b' :=
        ⟨a.remove b hi,(a.retain_remove b hi).symm⟩
      rw [headBefore_fixed,headBefore_fixed,component_there,component_there]
      rw [← S.assoc,← D.snd_nat,S.assoc,logical_prefix]
  | inr hb =>
    obtain ⟨b,rfl⟩ := hb
    cases b with
    | here =>
      rw [logical_first,← S.assoc,ExchangeScript.component,headBefore_tail,headBefore_tail,
        component_there,component_there]
      rw [← S.assoc (M.tensor (S.id C) (logicalSide o a.erase U A B)),← D.snd_nat]
      have hr := congrArg (fun k => S.comp (D.snd C (fold o (a.erase ++ o.formula A B :: U))) k)
        (logical_first o a.erase U A B)
      cases o <;> dsimp only [S,side,category,opposite] at hr ⊢
      all_goals simpa only [Laws.assoc] using hr.symm
    | there b => cases b with
      | here =>
        rw [logical_second,← S.assoc,ExchangeScript.component,headBefore_tail,headBefore_tail,
          component_there,component_there]
        rw [← S.assoc (M.tensor (S.id C) (logicalSide o a.erase U A B)),← D.snd_nat]
        have hr := congrArg (fun k => S.comp (D.snd C (fold o (a.erase ++ o.formula A B :: U))) k)
          (logical_second o a.erase U A B)
        cases o <;> dsimp only [S,side,category,opposite] at hr ⊢
        all_goals simpa only [Laws.assoc] using hr.symm
      | there b =>
        have hl : S.comp (logicalSide o F U A B) (component o (At.shift F (.there (.there b)))) =
            component o (At.shift F (.there b)) := by
          simpa only [At.shift] using logical_tail o F U A B b
        have hr : S.comp (logicalSide o a.erase U A B)
            (component o (At.shift a.erase (.there (.there b)))) =
            component o (At.shift a.erase (.there b)) := by
          simpa only [At.shift] using logical_tail o a.erase U A B b
        rw [hl,ExchangeScript.component,headBefore_tail,headBefore_tail,component_there,component_there]
        rw [← S.assoc,← D.snd_nat,S.assoc,hr]

end LogicalDeletion
end DosenPetric.Reduced.Gentzen
