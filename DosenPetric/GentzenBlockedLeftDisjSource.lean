module

public import DosenPetric.GentzenSelectedRouteVector

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.BlockedLeftDisj
universe u
variable {P : Type u}

theorem source_denote {K F U D E : List (NormalForm P)} {A B C : NormalForm P}
    (r : Route K (F++U)) (x : At K C) (a : At F C) (b : At U C)
    (p : Route x.erase a.erase) (q : Route x.erase b.erase)
    (ha : r.firstBlock.get a = x) (hb : r.secondBlock.get b = x)
    (hp : ∀ {V : NormalForm P} (v : At a.erase V),
      r.firstBlock.get (a.retain v) = x.retain (p.get v))
    (hq : ∀ {V : NormalForm P} (v : At b.erase V),
      r.secondBlock.get (b.retain v) = x.retain (q.get v))
    (f : G P (F++[A]) D) (g : G P (U++[B]) E) :
    comp ((LogicalDeletion.headBefore x [.disj A B]).arrow .conj)
      (comp ((r.parallel (Route.identity [.disj A B])).sideArrow .conj)
        (ofTerm (BlockedSource.disjLLast f g).denote)) =
      ofTerm (headParent p q ((LogicalDeletion.headBefore a [A]).left f)
        ((LogicalDeletion.headBefore b [B]).left g)).denote := by
  have hv := Route.selected_blocks_factor r x a b p q ha hb hp hq
  have he := congrArg (fun t => (t.parallel (Route.identity [.disj A B])).sideArrow .conj) hv
  rw [← Route.parallel_compose_fixed,← Route.parallel_compose_fixed,
    Route.compose_side,Route.compose_side] at he
  dsimp only [side,category] at he
  rw [headParent,StructuralProgram.left_denote,Route.program_arrow,
    LogicalDeletion.headBefore_route]
  rw [← Laws.assoc,he,Laws.assoc,Rules.terminalDisjLeft_denote]
  erw [Rules.terminalDisjLeft_nat]
  rw [Rules.terminalDisjLeft_denote]
  apply congrArg (fun t => comp _ t)
  apply Rules.terminalDisjLeft_congr
  · simp only [ofTerm_comp,ExchangeScript.left_denote,LogicalDeletion.headBefore_route]
    rfl
  · simp only [ofTerm_comp,ExchangeScript.left_denote,LogicalDeletion.headBefore_route]
    rfl

end DosenPetric.Reduced.Gentzen.BlockedLeftDisj
