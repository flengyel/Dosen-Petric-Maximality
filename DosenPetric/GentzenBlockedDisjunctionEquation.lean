module

public import DosenPetric.GentzenSequentialRightRouteRepair

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.BlockedDisjunction
universe u
variable {P : Type u}

theorem selected_parent {A B : NormalForm P} {F X Y : List (NormalForm P)}
    (f : G P F (A::B::(X++.disj A B::Y))) :
    ofTerm ((block A B X Y).keep.toHead.right (parent f)).denote =
      ofTerm (((residue A B X Y).head (.disj A B)).program.right
        (SequentialDisjunction.parent (nativeChild f))).denote := by
  rw [ExchangeScript.right_denote,parent,ContractionBlock.denoteR,
    StructuralProgram.right_denote,Route.program_arrow]
  exact SequentialDisjunction.source_denote (block A B X Y).route (block A B X Y).keep
    (parametric A B X Y) (residue A B X Y) (fresh_get A B X Y) (parametric_get A B X Y)
    (fun v => residue_retained A B X Y v) f

theorem source_equation {A B : NormalForm P} {F X Y I J : List (NormalForm P)}
    (f : G P F (A::B::(X++.disj A B::Y))) (h : G P I J) (z : At I (.disj A B)) :
    ofTerm (PositionalCut.cut (parent f) (block A B X Y).keep h z).denote =
      ofTerm (SequentialRepair.prefixRouted (.disj A B) (residue A B X Y)
        (G.cut (SequentialDisjunction.fresh (G.cut (nativeChild f) (z.toHead.left h)))
          (z.toHead.left h))).denote := by
  apply (Rules.cut_congr (selected_parent f) (g := (z.toHead.left h).denote) rfl).trans
  exact SequentialDisjunction.routed_equation (residue A B X Y) (nativeChild f) h z

end DosenPetric.Reduced.Gentzen.BlockedDisjunction
