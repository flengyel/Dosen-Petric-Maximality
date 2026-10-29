module

public import DosenPetric.GentzenBlockedLeftDisjSelectedEquation
public import DosenPetric.GentzenTerminalCutDescent

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.BlockedLeftDisj
universe u
variable {P : Type u}

def gammaParent {A B C : NormalForm P} {X Y Z T D E : List (NormalForm P)}
    (f : G P ((X++C::Y)++[A]) D) (g : G P ((Z++C::T)++[B]) E) :
    G P ((gaps [X,Y++Z]++C::T)++[.disj A B]) (D++E) :=
  ((BlockedMix.gammaBlock C Z T X Y).extend [.disj A B]).applyL (Nat.le_refl 2) _
    (BlockedSource.disjLLast f g)

theorem gammaParent_source {A B C : NormalForm P} {X Y Z T D E : List (NormalForm P)}
    (f : G P ((X++C::Y)++[A]) D) (g : G P ((Z++C::T)++[B]) E) :
    (gammaParent f g).reindex (by simp only [List.append_assoc,List.cons_append]) rfl =
      BlockedSource.left2 C X (Y++Z) (T++[.disj A B]) (D++E)
        ((BlockedSource.disjLLast f g).reindex
          (by simp only [List.append_assoc,List.cons_append]) rfl) := by
  simp only [gammaParent,BlockedMix.gammaBlock,ContractionBlock.extend,ContractionBlock.applyL,
    BlockedSource.left2,G.reindex_trans]
  rfl

theorem gamma_equation {A B C : NormalForm P} {X Y Z T D E I J : List (NormalForm P)}
    (f : G P ((X++C::Y)++[A]) D) (g : G P ((Z++C::T)++[B]) E) (h : G P I J) (z : At J C) :
    ofTerm (PositionalCut.cut h z (gammaParent f g)
      ((BlockedMix.gammaBlock C Z T X Y).keep.before [.disj A B])).denote =
      ofTerm (selectedParallel (BlockedMix.gammaBlock C Z T X Y).keep
        (BlockedMix.firstTag C X Y) (BlockedMix.firstTag C Z T)
        (BlockedMix.gammaSecondRoute C Z T X Y) (BlockedMix.gammaFirstRoute C Z T X Y)
        (PositionalCut.cut h z f ((BlockedMix.firstTag C X Y).before [A]))
        (PositionalCut.cut h z g ((BlockedMix.firstTag C Z T).before [B]))).denote := by
  apply selected_equation (BlockedMix.gammaBlock C Z T X Y).route
    (BlockedMix.gammaBlock C Z T X Y).keep (BlockedMix.firstTag C X Y) (BlockedMix.firstTag C Z T)
    (BlockedMix.gammaSecondRoute C Z T X Y) (BlockedMix.gammaFirstRoute C Z T X Y)
    (BlockedMix.gamma_second C Z T X Y) (BlockedMix.gamma_first C Z T X Y)
    (fun v => (Route.selectedResidual_get _ _ _ _ v).symm)
    (fun v => (Route.selectedResidual_get _ _ _ _ v).symm) f g (gammaParent f g)
  rw [gammaParent,ContractionBlock.denoteL,ContractionBlock.extend_route]
  rfl

end DosenPetric.Reduced.Gentzen.BlockedLeftDisj
