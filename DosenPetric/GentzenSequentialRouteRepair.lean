module

public import DosenPetric.GentzenSequentialConjunctionSource

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

namespace Route

theorem head_singleFiber {K F : List (NormalForm P)} (C : NormalForm P) (p : Route K F) :
    (p.head C).program.route.SingleFiber (.here C K) (.here C F) := by
  apply singleFiber_of_unique
  · rw [StructuralProgram.route_get,program_get,head_here]
  · intro b hb
    rw [StructuralProgram.route_get,program_get] at hb
    cases b with
    | here => rfl
    | there b => rw [head_there] at hb; cases hb

end Route
namespace SequentialRepair

def routed {K F D I R : List (NormalForm P)} (C : NormalForm P) (p : Route K F)
    (g : G P ((F++I)++I) ((D++R)++R)) : G P (K++I) (D++R) :=
  ((((p.head C).program.residual (.here C K) (.here C F) (p.head_singleFiber C)).suffixFixed I).left
    (repair g))

theorem routed_count {K F D I R : List (NormalForm P)} (C : NormalForm P) (p : Route K F)
    (g : G P ((F++I)++I) ((D++R)++R)) : (routed C p g).cutCount = g.cutCount := by
  rw [routed,StructuralProgram.left_count,repair_count]

theorem routed_congr {K F D I R : List (NormalForm P)} (C : NormalForm P) (p : Route K F)
    (g g' : G P ((F++I)++I) ((D++R)++R))
    (he : ofTerm g.denote = ofTerm g'.denote) :
    ofTerm (routed C p g).denote = ofTerm (routed C p g').denote := by
  rw [routed,routed,StructuralProgram.left_denote,StructuralProgram.left_denote,repair_congr g g' he]

end SequentialRepair
end DosenPetric.Reduced.Gentzen
