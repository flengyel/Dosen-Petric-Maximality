module

public import DosenPetric.GentzenLogicalDeletionPrefix

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace LogicalDeletion

/-- A suffix selection below a specified logical middle block. -/
def headUnder (F M : List (NormalForm P)) {U : List (NormalForm P)} {C : NormalForm P}
    (a : At U C) : ExchangeScript P (C :: (F ++ (M ++ a.erase))) (F ++ (M ++ U)) :=
  (At.shift F (At.shift M a)).toHead.reindex
    (congrArg (List.cons C) (At.erase_shift_twice F M a)) rfl

theorem headUnder_index (F M : List (NormalForm P)) {U : List (NormalForm P)}
    {C E : NormalForm P} (a : At U C) (b : At (F ++ (M ++ U)) E) :
    ((headUnder F M a).get b).index = exchangeIndex 0 (F.length + M.length + a.index) 1 b.index := by
  change (((At.shift F (At.shift M a)).toHead.get b).cast _).index = _
  rw [At.index_cast,At.toHead_get_index,At.index_shift,At.index_shift,Nat.add_assoc]

theorem headUnder_before (F M : List (NormalForm P)) {U : List (NormalForm P)}
    {C E : NormalForm P} (a : At U C) (b : At F E) :
    (headUnder F M a).get (b.before (M ++ U)) = .there (b.before (M ++ a.erase)) := by
  apply At.index_injective
  rw [headUnder_index,At.index_before]
  simp only [At.index,At.index_before]
  have hi := b.index_lt
  unfold exchangeIndex
  split <;> (try split) <;> (try split) <;> omega

theorem headUnder_middle (F M : List (NormalForm P)) {U : List (NormalForm P)}
    {C E : NormalForm P} (a : At U C) (b : At M E) :
    (headUnder F M a).get (At.shift F (b.before U)) = .there (At.shift F (b.before a.erase)) := by
  apply At.index_injective
  rw [headUnder_index,At.index_shift,At.index_before]
  simp only [At.index,At.index_shift,At.index_before]
  have hi := b.index_lt
  unfold exchangeIndex
  split <;> (try split) <;> (try split) <;> omega

theorem headUnder_selected (F M : List (NormalForm P)) {U : List (NormalForm P)}
    {C : NormalForm P} (a : At U C) :
    (headUnder F M a).get (At.shift F (At.shift M a)) = .here C (F ++ (M ++ a.erase)) := by
  apply At.index_injective
  rw [headUnder_index,At.index_shift,At.index_shift]
  simp only [At.index,exchangeIndex,Nat.zero_add]
  split <;> (try split) <;> (try split) <;> omega

theorem headUnder_fixed (F M : List (NormalForm P)) {U : List (NormalForm P)}
    {C E : NormalForm P} (a : At U C) (b : At a.erase E) :
    (headUnder F M a).get (At.shift F (At.shift M (a.retain b))) =
      .there (At.shift F (At.shift M b)) := by
  apply At.index_injective
  rw [headUnder_index,At.index_shift,At.index_shift,At.retain_index]
  simp only [At.index,At.index_shift]
  unfold exchangeIndex
  split <;> (try split) <;> (try split) <;> (try split) <;> omega

/-- Delete a nonprincipal suffix tag through either native unary logical comparison. -/
theorem tail_square (o : Op) (F : List (NormalForm P)) {U : List (NormalForm P)}
    (A B : NormalForm P) {C : NormalForm P} (a : At U C) :
    (side P o).comp ((headUnder F [o.formula A B] a).arrow o) (logicalSide o F U A B) =
      (side P o).comp ((sideM P o).tensor ((side P o).id C) (logicalSide o F a.erase A B))
        ((headUnder F [A,B] a).arrow o) := by
  let S := side P o
  let M := sideM P o
  let D := sideD P o
  apply side_ext o
  intro E b
  rw [S.assoc,S.assoc,ExchangeScript.component]
  cases At.cases_append F (A :: B :: U) b with
  | inl hb =>
    obtain ⟨b,rfl⟩ := hb
    have hp : (headUnder F [o.formula A B] a).get (b.before (o.formula A B :: U)) =
        .there (b.before (o.formula A B :: a.erase)) := headUnder_before F [o.formula A B] a b
    have hq : (headUnder F [A,B] a).get (b.before (A :: B :: U)) =
        .there (b.before (A :: B :: a.erase)) := headUnder_before F [A,B] a b
    rw [logical_prefix,ExchangeScript.component,hp,hq,component_there,component_there]
    rw [← S.assoc,← D.snd_nat,S.assoc,logical_prefix]
    all_goals rfl
  | inr hb =>
    obtain ⟨b,rfl⟩ := hb
    cases b with
    | here =>
      have hp : (headUnder F [o.formula A B] a).get (At.shift F (.here (o.formula A B) U)) =
          .there (At.shift F (.here (o.formula A B) a.erase)) := by
        simpa only [At.before,List.nil_append] using headUnder_middle F [o.formula A B] a (.here (o.formula A B) [])
      have hq : (headUnder F [A,B] a).get (At.shift F (.here A (B :: U))) =
          .there (At.shift F (.here A (B :: a.erase))) := by
        simpa only [At.before,List.singleton_append] using headUnder_middle F [A,B] a (.here A [B])
      rw [logical_first,← S.assoc,ExchangeScript.component,hp,hq,component_there,component_there]
      rw [← S.assoc (M.tensor (S.id C) (logicalSide o F a.erase A B)),← D.snd_nat]
      have hr := congrArg (fun k => S.comp (D.snd C (fold o (F ++ o.formula A B :: a.erase))) k)
        (logical_first o F a.erase A B)
      cases o <;> dsimp only [S,D,side,category,opposite] at hr ⊢
      all_goals simpa only [List.singleton_append,Laws.assoc] using hr.symm
    | there b => cases b with
      | here =>
        have hp : (headUnder F [o.formula A B] a).get (At.shift F (.here (o.formula A B) U)) =
            .there (At.shift F (.here (o.formula A B) a.erase)) := by
          simpa only [At.before,List.nil_append] using headUnder_middle F [o.formula A B] a (.here (o.formula A B) [])
        have hq : (headUnder F [A,B] a).get (At.shift F (.there (.here B U))) =
            .there (At.shift F (.there (.here B a.erase))) := by
          simpa only [At.before,List.nil_append] using headUnder_middle F [A,B] a (.there (.here B []))
        rw [logical_second,← S.assoc,ExchangeScript.component,hp,hq,component_there,component_there]
        rw [← S.assoc (M.tensor (S.id C) (logicalSide o F a.erase A B)),← D.snd_nat]
        have hr := congrArg (fun k => S.comp (D.snd C (fold o (F ++ o.formula A B :: a.erase))) k)
          (logical_second o F a.erase A B)
        cases o <;> dsimp only [S,D,side,category,opposite] at hr ⊢
        all_goals simpa only [List.singleton_append,Laws.assoc] using hr.symm
      | there b =>
        have hl : S.comp (logicalSide o F U A B) (component o (At.shift F (.there (.there b)))) =
            component o (At.shift F (.there b)) := by
          simpa only [At.shift] using logical_tail o F U A B b
        rw [hl,ExchangeScript.component]
        by_cases hi : b.index = a.index
        · have he := b.formula_eq a hi
          cases he
          have he : b = a := by apply At.index_injective; exact hi
          cases he
          have hp : (headUnder F [o.formula A B] a).get (At.shift F (.there a)) =
              .here C (F ++ o.formula A B :: a.erase) := by
            simpa only [At.shift,List.singleton_append] using headUnder_selected F [o.formula A B] a
          have hq : (headUnder F [A,B] a).get (At.shift F (.there (.there a))) =
              .here C (F ++ A :: B :: a.erase) := by
            simpa only [At.shift,List.cons_append,List.nil_append] using headUnder_selected F [A,B] a
          rw [hp,hq,component_here,component_here,← D.fst_nat,S.comp_id]
        · obtain ⟨b,rfl⟩ : ∃ b' : At a.erase E, b = a.retain b' :=
            ⟨a.remove b hi,(a.retain_remove b hi).symm⟩
          have hp : (headUnder F [o.formula A B] a).get (At.shift F (.there (a.retain b))) =
              .there (At.shift F (.there b)) := by
            simpa only [At.shift] using headUnder_fixed F [o.formula A B] a b
          have hq : (headUnder F [A,B] a).get (At.shift F (.there (.there (a.retain b)))) =
              .there (At.shift F (.there (.there b))) := by
            simpa only [At.shift] using headUnder_fixed F [A,B] a b
          have hr : S.comp (logicalSide o F a.erase A B)
              (component o (At.shift F (.there (.there b)))) = component o (At.shift F (.there b)) := by
            simpa only [At.shift] using logical_tail o F a.erase A B b
          rw [hp,hq,component_there,component_there]
          rw [← S.assoc,← D.snd_nat,S.assoc,hr]
          all_goals rfl

end LogicalDeletion
end DosenPetric.Reduced.Gentzen
