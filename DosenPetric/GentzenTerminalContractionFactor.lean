module

public import DosenPetric.GentzenBlockedDisjunctionRank

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.SequentialLogical
universe u
variable {P : Type u}

theorem terminal_contraction_factor (o : Op) {K F : List (NormalForm P)} {C : NormalForm P}
    (r : Route K (F++[C])) (x : At K C) (a : At F C) (p : Route x.erase a.erase)
    (ha : r.firstBlock.get a = x) (hb : r.secondBlock.get (.here C []) = x)
    (hp : ∀ {E : NormalForm P} (v : At a.erase E),
      r.firstBlock.get (a.retain v) = x.retain (p.get v)) :
    (side P o).comp (x.toHead.arrow o) (r.sideArrow o) =
      (side P o).comp ((p.head C).sideArrow o)
        ((side P o).comp ((SequentialRepair.headBlock C a.erase).route.sideArrow o)
          ((principal a C).arrow o)) := by
  let S := side P o
  have hv := Route.selected_blocks_factor r x a (.here C []) p .nil ha hb hp (fun v => nomatch v)
  change x.toHead.route.compose r =
    ((p.head C).append (.cons (.here C x.erase) .nil)).compose
      (a.toHead.route.parallel (Route.identity [C])) at hv
  rw [duplicated_head_terminal] at hv
  have he := congrArg (fun s => s.sideArrow o) hv
  rw [Route.compose_side,ExchangeScript.route_arrow,Route.compose_side,Route.compose_side,
    Route.compose_side,ExchangeScript.route_arrow,← LogicalDeletion.headBefore_route] at he
  rw [he,principal,ExchangeScript.seq_side_arrow,S.assoc,S.assoc]

theorem principal_selected {F : List (NormalForm P)} {C : NormalForm P} (a : At F C)
    (Q : NormalForm P) : (principal a Q).get (a.before [Q]) = .here C (Q::a.erase) := by
  change ((BinaryMix.swapWhole a.erase [Q]).consFixed C).get
    ((LogicalDeletion.headBefore a [Q]).get (a.before [Q])) = _
  rw [LogicalDeletion.headBefore_selected,ExchangeScript.consFixed_here]
  rfl

theorem principal_fixed {F : List (NormalForm P)} {C E : NormalForm P} (a : At F C)
    (Q : NormalForm P) (v : At a.erase E) :
    (principal a Q).get ((a.retain v).before [Q]) = .there (.there v) := by
  change ((BinaryMix.swapWhole a.erase [Q]).consFixed C).get
    ((LogicalDeletion.headBefore a [Q]).get ((a.retain v).before [Q])) = _
  rw [LogicalDeletion.headBefore_fixed,ExchangeScript.consFixed_there,BinaryMix.swapWhole_before]
  rfl

theorem principal_tail {F : List (NormalForm P)} {C : NormalForm P} (a : At F C)
    (Q : NormalForm P) : (principal a Q).get (At.shift F (.here Q [])) = .there (.here Q a.erase) := by
  change ((BinaryMix.swapWhole a.erase [Q]).consFixed C).get
    ((LogicalDeletion.headBefore a [Q]).get (At.shift F (.here Q []))) = _
  rw [LogicalDeletion.headBefore_tail,ExchangeScript.consFixed_there,BinaryMix.swapWhole_shift]
  rfl

theorem principal_factor (o : Op) {F : List (NormalForm P)} {C : NormalForm P}
    (a : At F C) (Q : NormalForm P) :
    (principal a Q).arrow o = (side P o).comp ((HeadRouting.front [Q] a.erase C).arrow o)
      ((side P o).comp ((a.toHead.consFixed Q).arrow o) ((BinaryMix.swapWhole F [Q]).arrow o)) := by
  have hg {E : NormalForm P} (v : At (F++[Q]) E) :
      (principal a Q).get v = (HeadRouting.front [Q] a.erase C).get
        ((a.toHead.consFixed Q).get ((BinaryMix.swapWhole F [Q]).get v)) := by
    cases At.cases_append F [Q] v with
    | inl hv =>
      obtain ⟨v,rfl⟩ := hv
      rw [BinaryMix.swapWhole_before]
      change (principal a Q).get (v.before [Q]) = (HeadRouting.front [Q] a.erase C).get
        ((a.toHead.consFixed Q).get (.there v))
      rw [ExchangeScript.consFixed_there]
      by_cases hi : v.index = a.index
      · have he := v.formula_eq a hi
        cases he
        have hv : v = a := At.index_injective v a hi
        cases hv
        rw [principal_selected,At.toHead_get]
        exact (HeadRouting.front_head [Q] a.erase C).symm
      · obtain ⟨v,rfl⟩ : ∃ v' : At a.erase E, v = a.retain v' :=
          ⟨a.remove v hi,(a.retain_remove v hi).symm⟩
        rw [principal_fixed,At.toHead_get_retain]
        exact (HeadRouting.front_tail [Q] a.erase C v).symm
    | inr hv =>
      obtain ⟨v,rfl⟩ := hv
      cases v with
      | here =>
        rw [principal_tail,BinaryMix.swapWhole_shift]
        change .there (.here Q a.erase) = (HeadRouting.front [Q] a.erase C).get
          ((a.toHead.consFixed Q).get (.here Q F))
        rw [ExchangeScript.consFixed_here]
        exact (HeadRouting.front_before a.erase C (.here Q [])).symm
      | there v => cases v
  let S := side P o
  apply side_ext o
  intro E v
  rw [ExchangeScript.component]
  change component o ((principal a Q).get v) = S.comp
    (S.comp ((HeadRouting.front [Q] a.erase C).arrow o)
      (S.comp ((a.toHead.consFixed Q).arrow o) ((BinaryMix.swapWhole F [Q]).arrow o))) (component o v)
  rw [S.assoc,S.assoc,hg]
  dsimp only [S]
  rw [ExchangeScript.component,ExchangeScript.component,ExchangeScript.component]

end DosenPetric.Reduced.Gentzen.SequentialLogical
