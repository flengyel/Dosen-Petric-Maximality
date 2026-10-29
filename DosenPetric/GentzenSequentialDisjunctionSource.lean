module

public import DosenPetric.GentzenFreshDisjunctionRecursion

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.SequentialDisjunction
universe u
variable {P : Type u}

theorem principal_body {F U : List (NormalForm P)} {A B : NormalForm P}
    (a : At U (.disj A B)) (f : G P F (A::B::U)) :
    comp (ofTerm (G.disjR F [] U A B f).denote) ((LogicalDeletion.headUnder [] [.disj A B] a).arrow .disj) =
      ofTerm (body ((LogicalDeletion.headUnder [] [A,B] a).structural.right f)).denote := by
  rw [body,G.denote_disjR,G.denote_disjR,StructuralProgram.right_denote,
    ExchangeScript.structural_arrow,disjRight_compare,disjRight_compare]
  have he := LogicalDeletion.tail_square .disj [] A B a
  rw [← logicalSide_cons] at he
  change comp (ofTerm (logicalCompare .disj [] U A B).invTerm)
      ((LogicalDeletion.headUnder [] [.disj A B] a).arrow .disj) =
    comp ((LogicalDeletion.headUnder [] [A,B] a).arrow .disj)
      (ofTerm (logicalCompare .disj [.disj A B] a.erase A B).invTerm) at he
  change comp (comp (ofTerm f.denote) (ofTerm (logicalCompare .disj [] U A B).invTerm))
      ((LogicalDeletion.headUnder [] [.disj A B] a).arrow .disj) =
    comp (comp (ofTerm f.denote) ((LogicalDeletion.headUnder [] [A,B] a).arrow .disj))
      (ofTerm (logicalCompare .disj [.disj A B] a.erase A B).invTerm)
  rw [Laws.assoc,he,← Laws.assoc]

theorem source_denote {K F U : List (NormalForm P)} {A B : NormalForm P}
    (r : Route K (.disj A B::U)) (x : At K (.disj A B)) (a : At U (.disj A B))
    (p : Route x.erase a.erase)
    (hf : r.get (.here (.disj A B) U) = x) (ha : r.get (.there a) = x)
    (hp : ∀ {E : NormalForm P} (v : At a.erase E), r.get (.there (a.retain v)) = x.retain (p.get v))
    (f : G P F (A::B::U)) :
    comp (comp (ofTerm (G.disjR F [] U A B f).denote) (r.sideArrow .disj)) (x.toHead.arrow .disj) =
      comp (ofTerm (parent ((LogicalDeletion.headUnder [] [A,B] a).structural.right f)).denote)
        ((p.head (.disj A B)).sideArrow .disj) := by
  have hv := SequentialLogical.front_contraction_factor r x a p hf ha hp
  have he := congrArg (fun s => s.sideArrow .disj) hv
  rw [Route.compose_side,Route.compose_side,Route.compose_side,
    ExchangeScript.route_arrow,ExchangeScript.route_arrow] at he
  change comp (r.sideArrow .disj) (x.toHead.arrow .disj) =
    comp (comp ((LogicalDeletion.headUnder [] [.disj A B] a).arrow .disj)
      ((SequentialRepair.headBlock (.disj A B) a.erase).route.sideArrow .disj))
      ((p.head (.disj A B)).sideArrow .disj) at he
  rw [Laws.assoc,he,← Laws.assoc,← Laws.assoc,principal_body,parent,
    SequentialRepair.headParentRight,ContractionBlock.denoteR]
  rfl

end DosenPetric.Reduced.Gentzen.SequentialDisjunction
