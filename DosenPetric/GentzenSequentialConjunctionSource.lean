module

public import DosenPetric.GentzenSequentialContractionRoute

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.SequentialConjunction
universe u
variable {P : Type u}

theorem principal_body {F D : List (NormalForm P)} {A B : NormalForm P}
    (a : At F (.conj A B)) (f : G P (F++[A,B]) D) :
    comp ((SequentialLogical.principal a (.conj A B)).arrow .conj)
      (ofTerm (BlockedSource.conjLLast F D A B f).denote) =
      ofTerm (body ((SequentialLogical.components a A B).structural.left f)).denote := by
  rw [BlockedSource.conjLLast,body,G.denote_conjL,G.denote_conjL,
    StructuralProgram.left_denote,ExchangeScript.structural_arrow,conjLeft_compare,conjLeft_compare]
  have he := SequentialLogical.principal_square .conj a A B
  change comp ((SequentialLogical.principal a (.conj A B)).arrow .conj)
      (ofTerm (logicalCompare .conj F [] A B).toTerm) =
    comp (ofTerm (logicalCompare .conj [.conj A B] a.erase A B).toTerm)
      ((SequentialLogical.components a A B).arrow .conj) at he
  rw [← Laws.assoc,he,Laws.assoc]

theorem source_denote {K F D : List (NormalForm P)} {A B : NormalForm P}
    (r : Route K (F++[.conj A B])) (x : At K (.conj A B)) (a : At F (.conj A B))
    (p : Route x.erase a.erase)
    (ha : r.firstBlock.get a = x) (hb : r.secondBlock.get (.here (.conj A B) []) = x)
    (hp : ∀ {E : NormalForm P} (v : At a.erase E),
      r.firstBlock.get (a.retain v) = x.retain (p.get v))
    (f : G P (F++[A,B]) D) :
    comp (x.toHead.arrow .conj)
      (comp (r.sideArrow .conj) (ofTerm (BlockedSource.conjLLast F D A B f).denote)) =
      comp ((p.head (.conj A B)).sideArrow .conj)
        (ofTerm (parent ((SequentialLogical.components a A B).structural.left f)).denote) := by
  have hv := Route.selected_blocks_factor r x a (.here (.conj A B) []) p .nil ha hb hp
    (fun v => nomatch v)
  change x.toHead.route.compose r =
    ((p.head (.conj A B)).append (.cons (.here (.conj A B) x.erase) .nil)).compose
      (a.toHead.route.parallel (Route.identity [.conj A B])) at hv
  rw [SequentialLogical.duplicated_head_terminal] at hv
  have he := congrArg (fun s => s.sideArrow .conj) hv
  rw [Route.compose_side,ExchangeScript.route_arrow,Route.compose_side,Route.compose_side,
    Route.compose_side,ExchangeScript.route_arrow,← LogicalDeletion.headBefore_route] at he
  change comp (x.toHead.arrow .conj) (r.sideArrow .conj) =
    comp (comp ((p.head (.conj A B)).sideArrow .conj)
      (comp ((SequentialRepair.headBlock (.conj A B) a.erase).route.sideArrow .conj)
        (((BinaryMix.swapWhole a.erase [.conj A B]).consFixed (.conj A B)).arrow .conj)))
      ((LogicalDeletion.headBefore a [.conj A B]).arrow .conj) at he
  rw [← Laws.assoc,he]
  simp only [Laws.assoc]
  rw [← Laws.assoc (((BinaryMix.swapWhole a.erase [.conj A B]).consFixed (.conj A B)).arrow .conj)]
  have hs := principal_body a f
  rw [SequentialLogical.principal,ExchangeScript.seq_side_arrow] at hs
  dsimp only [side,category] at hs
  rw [hs,parent,SequentialRepair.headParent,ContractionBlock.denoteL]
  rfl

end DosenPetric.Reduced.Gentzen.SequentialConjunction
