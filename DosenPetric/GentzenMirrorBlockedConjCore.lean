module

public import DosenPetric.GentzenMirrorBlockedConjLift

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.MirrorCalculus.BlockedConj
universe u
variable {P : Type u}

def sharedParent {C Y F H A B D E : NormalForm P} (p : Hom Y F) (q : Hom Y H)
    (f : Hom (.conj C F) (.disj A D)) (g : Hom (.conj C H) (.disj B E)) :
    Hom (.conj C Y) (.disj (.conj A B) (.disj D E)) :=
  comp (pair (comp (tensor .conj (id C) p) f) (comp (tensor .conj (id C) q) g))
    (mixedDisj A D B E)

/-- Duplicate the original opposite premise only after selecting its exact
    residual context. The common splice kernel is shared by both branches. -/
theorem shared_splice {C Y F H A B D E X R : NormalForm P}
    (p : Hom Y F) (q : Hom Y H)
    (f : Hom (.conj C F) (.disj A D)) (g : Hom (.conj C H) (.disj B E))
    (h : Hom X (.disj C R)) :
    comp (splice h (sharedParent p q f g)) (assocL .disj (.conj A B) (.disj D E) R) =
      comp (BlockedMix.sharedInput q p)
        (comp (tensor .conj
          (comp (splice h f) (assocL .disj A D R))
          (comp (splice h g) (assocL .disj B E R)))
          (comp (mixedDisj A (.disj D R) B (.disj E R))
            (tensor .disj (id (.conj A B)) (BlockedMix.sharedOutput D E R)))) := by
  let k := splice h (id (.conj C Y))
  have hk {V : NormalForm P} (v : Hom (.conj C Y) V) :
      splice h v = comp k (tensor .disj v (id R)) := by
    have he := Splice.output h (id (.conj C Y)) v
    rw [Laws.id_comp] at he
    exact he
  have hf : comp (tensor .conj p (id X))
      (comp (splice h f) (assocL .disj A D R)) =
      comp k (lift (comp (tensor .conj (id C) p) f) R) := by
    rw [← Laws.assoc,← Splice.context,hk]
    exact Laws.assoc _ _ _
  have hg : comp (tensor .conj q (id X))
      (comp (splice h g) (assocL .disj B E R)) =
      comp k (lift (comp (tensor .conj (id C) q) g) R) := by
    rw [← Laws.assoc,← Splice.context,hk]
    exact Laws.assoc _ _ _
  unfold BlockedMix.sharedInput
  rw [← Laws.assoc (pair (tensor .conj p (id X)) (tensor .conj q (id X))),
    MirrorCalculus.pair_tensor,hf,hg,← ProductCalculation.pair_pre,Laws.assoc,lifted_pair]
  rw [hk]
  exact Laws.assoc _ _ _

end DosenPetric.Reduced.Gentzen.MirrorCalculus.BlockedConj
