module

public import DosenPetric.GentzenProductCalculations

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace PrincipalConjunction

variable {T A B D E V X Y : NormalForm P}

def body (h : Hom (.conj A (.conj B T)) V) : Hom (.conj T (.conj A B)) V :=
  comp (swap .conj T (.conj A B)) (comp (assocL .conj A B T) h)

def component (h : Hom (.conj A (.conj B T)) V) :
    Hom (.conj (.conj T (.disj A D)) B) (.disj V D) :=
  comp (ProductCalculation.rotate T (.disj A D) B)
    (comp (dist (.conj B T) A D) (tensor .disj (comp (swap .conj (.conj B T) A) h) (id D)))

theorem tensor_first_factor (o : Op) {A B C D E : NormalForm P}
    (f : Hom A B) (g : Hom B C) (h : Hom D E) :
    tensor o (comp f g) h = comp (tensor o f h) (tensor o g (id E)) := by
  rw [Laws.tensor_comp, Laws.comp_id]

/-- The structural adapters turn the distribution square into two component cuts. -/
theorem component_equation (h : Hom (.conj A (.conj B T)) V) :
    comp (CutDistribution.sequential T A D B) (tensor .disj (body h) (id D)) =
      component h := by
  unfold CutDistribution.sequential CutDistribution.stepWithContext body component
  simp only [Laws.assoc]
  rw [Laws.tensor_comp, Laws.id_comp]
  have hf : comp (CutDistribution.finish T B A)
      (comp (swap .conj T (.conj A B)) (comp (assocL .conj A B T) h)) =
      comp (tensor .conj (swap .conj T B) (id A)) (comp (swap .conj (.conj B T) A) h) := by
    simpa only [Laws.assoc] using congrArg (fun k => comp k h)
      (ProductCalculation.principal_finish T B A)
  rw [hf, tensor_first_factor .disj]
  rw [← Laws.assoc (dist (.conj T B) A D), Laws.dist_nat]
  rw [Laws.tensor_id]
  have hi := congrArg (fun k => comp k
    (comp (dist (.conj B T) A D)
      (tensor .disj (comp (swap .conj (.conj B T) A) h) (id D))))
    (ProductCalculation.principal_input T (.disj A D) B)
  simpa only [Laws.assoc, ProductCalculation.rotate] using hi

def normal (f : Hom X (.disj A D)) (g : Hom Y (.disj B E))
    (h : Hom (.conj A (.conj B T)) V) : Hom (.conj T (.conj X Y)) (.disj V (.disj D E)) :=
  comp (tensor .conj (id T) (tensor .conj f g))
    (comp (assocR .conj T (.disj A D) (.disj B E))
      (comp (dist (.conj T (.disj A D)) B E)
        (comp (tensor .disj (component h) (id E)) (assocL .disj V D E))))

theorem left_normal (f : Hom X (.disj A D)) (g : Hom Y (.disj B E))
    (h : Hom (.conj A (.conj B T)) V) :
    splice (comp (tensor .conj f g) (ofTerm (Term.mixedDisj A D B E)))
        (comp (assocL .conj A B T) h) = normal f g h := by
  rw [Splice.input]
  unfold splice
  change comp (tensor .conj (id T) (tensor .conj f g))
    (comp (tensor .conj (id T) (ofTerm (Term.mixedDisj A D B E)))
      (comp (dist T (.conj A B) (.disj D E)) (tensor .disj (body h) (id (.disj D E))))) = _
  rw [← Laws.assoc (tensor .conj (id T) (ofTerm (Term.mixedDisj A D B E))),
    CutDistribution.mixed_strength]
  simp only [Laws.assoc]
  have he : comp (assocL .disj (.conj T (.conj A B)) D E)
      (tensor .disj (body h) (id (.disj D E))) =
      comp (tensor .disj (tensor .disj (body h) (id D)) (id E)) (assocL .disj V D E) := by
    simpa only [Laws.tensor_id] using Laws.assocL_nat .disj (body h) (id D) (id E)
  rw [he]
  rw [← Laws.assoc (tensor .disj (CutDistribution.sequential T A D B) (id E)),
    Laws.tensor_comp, Laws.id_comp, component_equation]
  rfl

def inner (h : Hom (.conj A (.conj B T)) V) :
    Hom (.conj B (.conj T (.disj A D))) (.disj V D) :=
  comp (assocR .conj B T (.disj A D))
    (comp (dist (.conj B T) A D) (tensor .disj (comp (swap .conj (.conj B T) A) h) (id D)))

theorem inner_naturality (f : Hom X (.disj A D)) (h : Hom (.conj A (.conj B T)) V) :
    comp (assocR .conj B T X) (splice f h) =
      comp (tensor .conj (id B) (tensor .conj (id T) f)) (inner h) := by
  have he := congrArg (fun k => comp k
    (comp (dist (.conj B T) A D) (tensor .disj (comp (swap .conj (.conj B T) A) h) (id D))))
    (Laws.assocR_nat .conj (id B) (id T) f)
  simpa only [Laws.tensor_id, splice, inner, Laws.assoc] using he

theorem right_normal (f : Hom X (.disj A D)) (g : Hom Y (.disj B E))
    (h : Hom (.conj A (.conj B T)) V) :
    comp (assocR .conj T X Y)
        (comp (splice g (comp (assocR .conj B T X) (splice f h))) (assocL .disj V D E)) =
      normal f g h := by
  rw [inner_naturality, Splice.context]
  simp only [Laws.assoc]
  rw [← Laws.assoc (assocR .conj T X Y), Laws.assocR_nat]
  unfold splice
  simp only [Laws.assoc]
  have he : comp (assocR .conj T (.disj A D) Y)
      (tensor .conj (id (.conj T (.disj A D))) g) =
      comp (tensor .conj (id T) (tensor .conj (id (.disj A D)) g))
        (assocR .conj T (.disj A D) (.disj B E)) := by
    simpa only [Laws.tensor_id] using Laws.assocR_nat .conj (id T) (id (.disj A D)) g
  rw [← Laws.assoc (assocR .conj T (.disj A D) Y), he]
  simp only [Laws.assoc]
  rw [← Laws.assoc (tensor .conj (id T) (tensor .conj f (id Y))),
    Laws.tensor_comp, Laws.id_comp, Laws.tensor_comp, Laws.comp_id, Laws.id_comp]
  simp only [normal, component, inner, ProductCalculation.rotate, Laws.assoc]

/-- Principal conjunction reduction, before the canonical list-fold comparisons. -/
theorem equation (f : Hom X (.disj A D)) (g : Hom Y (.disj B E))
    (h : Hom (.conj A (.conj B T)) V) :
    splice (comp (tensor .conj f g) (ofTerm (Term.mixedDisj A D B E)))
        (comp (assocL .conj A B T) h) =
      comp (assocR .conj T X Y)
        (comp (splice g (comp (assocR .conj B T X) (splice f h))) (assocL .disj V D E)) :=
  (left_normal f g h).trans (right_normal f g h).symm

end PrincipalConjunction
end DosenPetric.Reduced.Gentzen
