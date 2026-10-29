module

public import DosenPetric.CartesianClosureObstruction

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.ExponentialData
universe u v
variable {P : Type u} {C : Category.{u,v} (Formula P)} {S : Structure C}
  {A B : Formula P} (E : ExponentialData S A B)

def toGlobalPoint (f : C.Hom A B) : C.Hom .top E.object := E.curry (C.comp (S.snd .top A) f)
def fromGlobalPoint (h : C.Hom .top E.object) : C.Hom A B :=
  C.comp (S.pair (S.toTop A) (C.id A)) (C.comp (S.prodMap h (C.id A)) E.evaluation)

theorem from_toGlobalPoint (f : C.Hom A B) : E.fromGlobalPoint (E.toGlobalPoint f) = f := by
  unfold fromGlobalPoint toGlobalPoint
  rw [E.beta,← C.assoc,S.pair_snd,C.id_comp]

theorem to_fromGlobalPoint (h : C.Hom .top E.object) : E.toGlobalPoint (E.fromGlobalPoint h) = h := by
  have hr : C.comp (S.snd .top A) (S.pair (S.toTop A) (C.id A)) = C.id (.conj .top A) := by
    apply S.pair_ext
    · rw [C.assoc,S.pair_fst,C.id_comp]
      exact (S.toTop_unique _).trans (S.toTop_unique _).symm
    · rw [C.assoc,S.pair_snd,C.comp_id,C.id_comp]
  unfold toGlobalPoint fromGlobalPoint
  rw [← C.assoc,hr,C.id_comp,E.eta]

end DosenPetric.ExponentialData
