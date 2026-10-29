module

public import DosenPetric.GentzenBlockedDisjunctionData

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace SequentialRepair

def prefixRouted {K D F I J : List (NormalForm P)} (C : NormalForm P) (p : Route K D)
    (g : G P (I++(I++F)) (J++(J++D))) : G P (I++F) (J++K) :=
  ((((p.head C).program.residual (.here C K) (.here C D) (p.head_singleFiber C)).prefixFixed J).right
    (prefixRepair g))

theorem prefixRouted_count {K D F I J : List (NormalForm P)} (C : NormalForm P) (p : Route K D)
    (g : G P (I++(I++F)) (J++(J++D))) : (prefixRouted C p g).cutCount = g.cutCount := by
  rw [prefixRouted,StructuralProgram.right_count,prefixRepair_count]

theorem prefixRouted_congr {K D F I J : List (NormalForm P)} (C : NormalForm P) (p : Route K D)
    (g g' : G P (I++(I++F)) (J++(J++D))) (he : ofTerm g.denote = ofTerm g'.denote) :
    ofTerm (prefixRouted C p g).denote = ofTerm (prefixRouted C p g').denote := by
  rw [prefixRouted,prefixRouted,StructuralProgram.right_denote,StructuralProgram.right_denote,
    prefixRepair_congr g g' he]

end SequentialRepair
namespace SequentialDisjunction

theorem routed_equation {K D F I J : List (NormalForm P)} {A B : NormalForm P}
    (p : Route K D) (f : G P F (.disj A B::A::B::D)) (h : G P I J) (z : At I (.disj A B)) :
    ofTerm (PositionalCut.cut ((p.head (.disj A B)).program.right (parent f))
      (.here (.disj A B) K) h z).denote =
      ofTerm (SequentialRepair.prefixRouted (.disj A B) p
        (G.cut (fresh (G.cut f (z.toHead.left h))) (z.toHead.left h))).denote := by
  apply (CutCommutation.same_right (p.head (.disj A B)).program _ _ (p.head_singleFiber (.disj A B))
    (parent f) h z).trans
  rw [SequentialRepair.prefixRouted,StructuralProgram.right_denote,StructuralProgram.right_denote]
  exact congrArg (fun k => comp k _) (native_equation f (z.toHead.left h))

end SequentialDisjunction
end DosenPetric.Reduced.Gentzen
