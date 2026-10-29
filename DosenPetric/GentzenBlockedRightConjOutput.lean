module

public import DosenPetric.GentzenBlockedRightConjNative

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.BlockedRightConj
universe u
variable {P : Type u}

theorem output_square {D E Y : List (NormalForm P)}
    (p : Route Y D) (q : Route Y E) (J : List (NormalForm P)) (Q : NormalForm P) :
    comp (tensor .disj (id Q)
      (tensor .disj (ofTerm (append .disj J D).toTerm) (ofTerm (append .disj J E).toTerm)))
      (comp (tensor .disj (id Q) (ofTerm (append .disj (J++D) (J++E)).toTerm))
        (comp (((BlockedMix.rightOutputRoute q p J).head Q).sideArrow .disj)
          ((HeadRouting.front J Y Q).inverse.arrow .disj))) =
      comp (sharedOutput (succ J) Q (p.sideArrow .disj) (q.sideArrow .disj))
        (ofTerm (append .disj J (Q::Y)).toTerm) := by
  have he := congrArg (fun k => comp (tensor .disj (id Q) k)
    ((HeadRouting.front J Y Q).inverse.arrow .disj)) (BlockedMix.right_output_square_disj q p J)
  simp only [tensor_factor .disj (id Q),Laws.assoc] at he
  rw [BinaryLogical.front_inverse_split] at he
  rw [Route.head_side]
  dsimp only [side,sideM,disjMonoidal,opposite,category]
  simpa only [sharedOutput,BlockedMix.rightSharedOutput,Laws.assoc] using he

end DosenPetric.Reduced.Gentzen.BlockedRightConj
