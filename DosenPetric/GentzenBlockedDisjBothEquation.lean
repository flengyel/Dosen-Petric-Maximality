module

public import DosenPetric.GentzenBlockedDisjBothData

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.BlockedDisjBoth
universe u
variable {P : Type u}

def firstChild {A B : NormalForm P} {X Y D : List (NormalForm P)}
    (f : G P ((X++.disj A B::Y)++[A]) D) :
    G P (.disj A B::((BlockedMix.firstTag (.disj A B) X Y).erase++[A])) D :=
  (LogicalDeletion.headBefore (BlockedMix.firstTag (.disj A B) X Y) [A]).left f

def secondChild {A B : NormalForm P} {Z T E : List (NormalForm P)}
    (g : G P ((Z++.disj A B::T)++[B]) E) :
    G P (.disj A B::((BlockedMix.firstTag (.disj A B) Z T).erase++[B])) E :=
  (LogicalDeletion.headBefore (BlockedMix.firstTag (.disj A B) Z T) [B]).left g

theorem selected_parent {A B : NormalForm P} {X Y Z T D E : List (NormalForm P)}
    (f : G P ((X++.disj A B::Y)++[A]) D) (g : G P ((Z++.disj A B::T)++[B]) E) :
    ofTerm ((block A B X Y Z T).keep.toHead.left (parent f g)).denote =
      ofTerm (SequentialDisjBoth.parent (firstResidue A B X Y Z T) (secondResidue A B X Y Z T)
        (firstChild f) (secondChild g)).denote := by
  rw [ExchangeScript.left_denote,parent,ContractionBlock.denoteL]
  exact SequentialDisjBoth.source_denote _ _ _ _ _ _
    (first_get A B X Y Z T) (second_get A B X Y Z T) (fresh_get A B X Y Z T)
    (fun v => (Route.selectedResidual_get _ _ _ _ v).symm)
    (fun v => (Route.selectedResidual_get _ _ _ _ v).symm) f g

theorem source_equation {A B : NormalForm P} {X Y Z T D E I J : List (NormalForm P)}
    (f : G P ((X++.disj A B::Y)++[A]) D) (g : G P ((Z++.disj A B::T)++[B]) E)
    (h : G P I J) (z : At J (.disj A B)) :
    ofTerm (PositionalCut.cut h z (parent f g) (block A B X Y Z T).keep).denote =
      ofTerm (SequentialDisjBoth.rebuild (.disj A B) (firstResidue A B X Y Z T) (secondResidue A B X Y Z T)
        (G.cut (z.toHead.right h) (SequentialDisjBoth.fresh
          (G.cut (z.toHead.right h) (firstChild f)) (G.cut (z.toHead.right h) (secondChild g))))).denote := by
  apply (Rules.cut_congr (f:=(z.toHead.right h).denote) rfl (selected_parent f g)).trans
  exact SequentialDisjBoth.native_equation (firstResidue A B X Y Z T) (secondResidue A B X Y Z T)
    (z.toHead.right h) (firstChild f) (secondChild g)

end DosenPetric.Reduced.Gentzen.BlockedDisjBoth
