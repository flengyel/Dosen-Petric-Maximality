module

public import DosenPetric.GentzenBlockedConjunctionData

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace SequentialConjunction

theorem routed_equation {K F D I J : List (NormalForm P)} {A B : NormalForm P}
    (p : Route K F) (f : G P (.conj A B::A::B::F) D) (h : G P I J) (z : At J (.conj A B)) :
    ofTerm (PositionalCut.cut h z ((p.head (.conj A B)).program.left (parent f))
      (.here (.conj A B) K)).denote =
      ofTerm (SequentialRepair.routed (.conj A B) p
        (G.cut (z.toHead.right h) (fresh (G.cut (z.toHead.right h) f)))).denote := by
  apply (CutCommutation.same_left (p.head (.conj A B)).program _ _ (p.head_singleFiber (.conj A B))
    h z (parent f)).trans
  rw [SequentialRepair.routed,StructuralProgram.left_denote,StructuralProgram.left_denote]
  exact congrArg (comp _) (native_equation f (z.toHead.right h))

end SequentialConjunction
namespace BlockedConjunction

def nativeChild {A B : NormalForm P} {X Y D : List (NormalForm P)}
    (f : G P ((X++.conj A B::Y)++[A,B]) D) :
    G P (.conj A B::A::B::(parametric A B X Y).erase) D :=
  (SequentialLogical.components (parametric A B X Y) A B).structural.left f

theorem selected_parent {A B : NormalForm P} {X Y D : List (NormalForm P)}
    (f : G P ((X++.conj A B::Y)++[A,B]) D) :
    ofTerm ((block A B X Y).keep.toHead.left (parent f)).denote =
      ofTerm (((residue A B X Y).head (.conj A B)).program.left
        (SequentialConjunction.parent (nativeChild f))).denote := by
  rw [ExchangeScript.left_denote,parent,ContractionBlock.denoteL,
    StructuralProgram.left_denote,Route.program_arrow]
  exact SequentialConjunction.source_denote (block A B X Y).route (block A B X Y).keep
    (parametric A B X Y) (residue A B X Y) (first_get A B X Y) (second_get A B X Y)
    (fun v => (Route.selectedResidual_get _ _ _ _ v).symm) f

theorem source_equation {A B : NormalForm P} {X Y D I J : List (NormalForm P)}
    (f : G P ((X++.conj A B::Y)++[A,B]) D) (h : G P I J) (z : At J (.conj A B)) :
    ofTerm (PositionalCut.cut h z (parent f) (block A B X Y).keep).denote =
      ofTerm (SequentialRepair.routed (.conj A B) (residue A B X Y)
        (G.cut (z.toHead.right h)
          (SequentialConjunction.fresh (G.cut (z.toHead.right h) (nativeChild f))))).denote := by
  apply (Rules.cut_congr (f := (z.toHead.right h).denote) rfl (selected_parent f)).trans
  exact SequentialConjunction.routed_equation (residue A B X Y) (nativeChild f) h z

end BlockedConjunction
end DosenPetric.Reduced.Gentzen
