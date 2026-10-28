module

import DosenPetric

set_option autoImplicit false
universe u
open DosenPetric DosenPetric.Reduced DosenPetric.Reduced.Gentzen

example {P : Type u} {A B X Y : NormalForm P} (h : Hom A B) (f g : Hom X Y) :
    tensor .conj h (union f g) = union (tensor .conj h f) (tensor .conj h g) :=
  MixCalculation.conj_union_right h f g

example {P : Type u} {A B X Y : NormalForm P} (f g : Hom A B) (h : Hom X Y) :
    tensor .conj (union f g) h = union (tensor .conj f h) (tensor .conj g h) :=
  MixCalculation.conj_union_left f g h

example {P : Type u} {A B X Y : NormalForm P} (h : Hom A B) (f g : Hom X Y) :
    tensor .disj h (union f g) = union (tensor .disj h f) (tensor .disj h g) :=
  MixCalculation.disj_union_right h f g

example {P : Type u} {A B X Y : NormalForm P} (f g : Hom A B) (h : Hom X Y) :
    tensor .disj (union f g) h = union (tensor .disj f h) (tensor .disj g h) :=
  MixCalculation.disj_union_left f g h

example {P : Type u} (A B : NormalForm P) :
    mix A B = union (comp (fst A B) (inl A B)) (comp (snd A B) (inr A B)) :=
  MixCalculation.mix_union A B

example {P : Type u} {X Y C D Z : NormalForm P} (f h : Hom X (.disj C D))
    (g : Hom (.conj C Y) Z) :
    splice (union f h) g = union (splice f g) (splice h g) :=
  MixCalculation.splice_union_left f h g

example {P : Type u} {X Y C D Z : NormalForm P} (f : Hom X (.disj C D))
    (g h : Hom (.conj C Y) Z) :
    splice f (union g h) = union (splice f g) (splice f h) :=
  MixCalculation.splice_union_right f g h

example {P : Type u} {Γ Θ Δ Λ : List (NormalForm P)} (f : G P Γ Δ) (g : G P Θ Λ) :
    ofTerm (G.mix f g).denote =
      union
        (comp (ofTerm (append .conj Θ Γ).invTerm)
          (comp (snd (ante Θ) (ante Γ))
            (comp (ofTerm f.denote)
              (comp (inr (succ Λ) (succ Δ)) (ofTerm (append .disj Λ Δ).toTerm)))))
        (comp (ofTerm (append .conj Θ Γ).invTerm)
          (comp (fst (ante Θ) (ante Γ))
            (comp (ofTerm g.denote)
              (comp (inl (succ Λ) (succ Δ)) (ofTerm (append .disj Λ Δ).toTerm))))) :=
  MixCalculation.native_mix_union f g

#print axioms MixCalculation.conj_union_right

#print axioms MixCalculation.conj_union_left

#print axioms MixCalculation.disj_union_right

#print axioms MixCalculation.disj_union_left

#print axioms MixCalculation.mix_union

#print axioms MixCalculation.splice_union_left

#print axioms MixCalculation.splice_union_right

#print axioms MixCalculation.native_mix_union
