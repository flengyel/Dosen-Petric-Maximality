module

public import DosenPetric.GentzenSequentialConjFirstSource

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace SequentialRepair

theorem headParentRight_congr {F D : List (NormalForm P)} {C : NormalForm P}
    (g g' : G P F (C::C::D)) (he : ofTerm g.denote = ofTerm g'.denote) :
    ofTerm (headParentRight g).denote = ofTerm (headParentRight g').denote := by
  rw [headParentRight,headParentRight,ContractionBlock.denoteR,ContractionBlock.denoteR,he]

theorem headParentRight_reindex {F V D : List (NormalForm P)} {C : NormalForm P}
    (he : D = V) (g : G P F (C::C::V)) :
    headParentRight (g.reindex rfl (congrArg (fun xs => C::C::xs) he.symm)) =
      (headParentRight g).reindex rfl (congrArg (List.cons C) he.symm) := by
  cases he
  rfl

theorem front_source_denote {K U F : List (NormalForm P)} {C : NormalForm P}
    (r : Route K (C::U)) (x : At K C) (a : At U C) (p : Route x.erase a.erase)
    (hf : r.get (.here C U) = x) (ha : r.get (.there a) = x)
    (hp : ∀ {E : NormalForm P} (v : At a.erase E), r.get (.there (a.retain v)) = x.retain (p.get v))
    (g : G P F (C::U)) :
    comp (comp (ofTerm g.denote) (r.sideArrow .disj)) (x.toHead.arrow .disj) =
      ofTerm ((p.head C).program.right (headParentRight ((LogicalDeletion.headUnder [] [C] a).right g))).denote := by
  have hv := SequentialLogical.front_contraction_factor r x a p hf ha hp
  have he := congrArg (fun s => s.sideArrow .disj) hv
  rw [Route.compose_side,Route.compose_side,Route.compose_side,
    ExchangeScript.route_arrow,ExchangeScript.route_arrow] at he
  change comp (r.sideArrow .disj) (x.toHead.arrow .disj) =
    comp (comp ((LogicalDeletion.headUnder [] [C] a).arrow .disj)
      ((headBlock C a.erase).route.sideArrow .disj)) ((p.head C).sideArrow .disj) at he
  rw [Laws.assoc,he,StructuralProgram.right_denote,Route.program_arrow,
    headParentRight,ContractionBlock.denoteR,ExchangeScript.right_denote]
  simp only [Laws.assoc]
  rfl

end SequentialRepair
namespace Route

theorem head_program_right_cast {K F V D : List (NormalForm P)} (C : NormalForm P)
    (p : Route K F) (he : F = V) (g : G P D (C::V)) :
    (p.head C).program.right (g.reindex rfl (congrArg (List.cons C) he.symm)) =
      ((p.cast rfl he).head C).program.right g := by
  cases he
  rfl

end Route
end DosenPetric.Reduced.Gentzen
