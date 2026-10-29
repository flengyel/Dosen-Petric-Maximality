module

public import DosenPetric.GentzenDisjFirstSelected

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.MirrorCalculus
universe u
variable {P : Type u}

def distRight (A B C : NormalForm P) : Hom (.conj (.disj A B) C) (.disj A (.conj B C)) :=
  Reduced.distRight (mirror C) (mirror B) (mirror A)

theorem distRight_eq (A B C : NormalForm P) :
    distRight A B C =
      comp (swap .conj (.disj A B) C)
        (comp (tensor .conj (id C) (swap .disj A B))
          (comp (dist C B A)
            (comp (tensor .disj (swap .conj C B) (id A)) (swap .disj (.conj B C) A)))) := by
  simp only [distRight,Reduced.distRight,Term.distRight,ofTerm_comp,ofTerm_tensor,ofTerm_id,
    term_swap,term_dist,comp,tensor,dist,swap,id,mirror,Reduced.Laws.assoc]

namespace Laws

theorem swap_swap (o : Op) (A B : NormalForm P) :
    comp (swap o A B) (swap o B A) = id (o.formula A B) := by
  cases o <;> exact Reduced.Laws.swap_swap _ _ _

theorem distRight_nat {A B C D E F : NormalForm P} (f : Hom A D) (g : Hom B E) (h : Hom C F) :
    comp (distRight A B C) (tensor .disj f (tensor .conj g h)) =
      comp (tensor .conj (tensor .disj f g) h) (distRight D E F) :=
  (Reduced.Laws.distRight_nat h g f).symm

theorem dist_b_conj (A B C D : NormalForm P) :
    comp (tensor .conj (dist A B C) (id D)) (distRight (.conj A B) C D) =
      comp (assocL .conj A (.disj B C) D)
        (comp (tensor .conj (id A) (distRight B C D)) (dist A B (.conj C D))) := by
  have he := congrArg (fun k => Reduced.comp k
    (Reduced.assocL .disj (mirror D) (.conj (mirror C) (mirror B)) (mirror A)))
      (Reduced.Laws.dist_b_disj (mirror D) (mirror C) (mirror B) (mirror A))
  simp only [Reduced.Laws.assoc] at he
  rw [Reduced.Laws.assocR_L,Reduced.Laws.comp_id] at he
  simpa only [comp,tensor,distRight,dist,id,assocL,mirror,Reduced.Laws.assoc] using he.symm

theorem dist_b_disj (A B C D : NormalForm P) :
    comp (dist (.disj A B) C D) (tensor .disj (distRight A B C) (id D)) =
      comp (distRight A B (.disj C D))
        (comp (tensor .disj (id A) (dist B C D)) (assocR .disj A (.conj B C) D)) := by
  have he := congrArg (fun k => Reduced.comp
    (Reduced.assocR .conj (mirror D) (.disj (mirror C) (mirror B)) (mirror A)) k)
      (Reduced.Laws.dist_b_conj (mirror D) (mirror C) (mirror B) (mirror A))
  conv at he =>
    rhs
    rw [← Reduced.Laws.assoc,Reduced.Laws.assocR_L,Reduced.Laws.id_comp]
  simpa only [comp,tensor,distRight,dist,id,assocR,mirror,Reduced.Laws.assoc] using he.symm

end Laws
end DosenPetric.Reduced.Gentzen.MirrorCalculus
