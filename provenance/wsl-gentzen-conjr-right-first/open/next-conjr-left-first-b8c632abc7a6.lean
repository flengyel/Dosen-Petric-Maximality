module
import DosenPetric.GentzenConjFirstSelected
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open DosenPetric DosenPetric.Reduced DosenPetric.Reduced.Gentzen
-- The first child's selected C is parametric; A remains a separate principal.
example {P : Type u} {A B C D E X Y T Z : NormalForm P}
    (f : Hom X (.disj A (.disj C D))) (g : Hom Y (.disj B E))
    (h : Hom (.conj C T) Z) :
    splice (comp (tensor .conj f g)
      (comp (ofTerm (Term.mixedDisj A (.disj C D) B E))
        (comp (tensor .disj (id (.conj A B)) (assocL .disj C D E))
          ((sideM P .disj).cross C (.conj A B) (.disj D E))))) h =
      comp (assocR .conj T X Y)
        (comp (tensor .conj
          (comp (splice (comp f ((sideM P .disj).cross C A D)) h)
            ((sideM P .disj).cross A Z D)) g)
          (comp (ofTerm (Term.mixedDisj A (.disj Z D) B E))
            (comp (tensor .disj (id (.conj A B)) (assocL .disj Z D E))
              ((sideM P .disj).cross Z (.conj A B) (.disj D E))))) := by
  rw [mixedDisj_eq,mixedDisj_eq]
  simp only [splice,innerDisj,sideM,disjMonoidal,opposite,category,
    MonoidalData.cross,Laws.assoc]
