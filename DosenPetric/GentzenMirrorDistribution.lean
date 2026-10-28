module

public import DosenPetric.GentzenMirrorSplice

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.MirrorCalculus
universe u
variable {P : Type u}
namespace CutDistribution

/-- Associating two strengths, with both comparison isomorphisms explicit. -/
theorem conjunction (T X B E : NormalForm P) :
    comp (tensor .conj (id T) (dist X B E)) (dist T (.conj X B) E) =
      comp (assocR .conj T X (.disj B E))
        (comp (dist (.conj T X) B E) (tensor .disj (assocL .conj T X B) (id E))) := by
  symm
  rw [Laws.dist_conj]
  simp only [Laws.assoc]
  rw [← Laws.assoc (assocR .conj T X (.disj B E)), Laws.assocR_L, Laws.id_comp]
  rw [Laws.tensor_comp, Laws.assocR_L, Laws.id_comp, Laws.tensor_id, Laws.comp_id]

/-- Associating a residual coproduct past strength. -/
theorem disjunction (T H D E : NormalForm P) :
    comp (tensor .conj (id T) (assocL .disj H D E)) (dist T H (.disj D E)) =
      comp (dist T (.disj H D) E)
        (comp (tensor .disj (dist T H D) (id E)) (assocL .disj (.conj T H) D E)) := by
  rw [Laws.dist_disj]
  rw [← Laws.assoc, Laws.tensor_comp, Laws.id_comp, Laws.assocL_R,
    Laws.tensor_id, Laws.id_comp]

/-- The inner component of mixed disjunction: first exchange, then distribute. -/
def step (A D B : NormalForm P) : Hom (.conj (.disj A D) B) (.disj (.conj A B) D) :=
  comp (swap .conj (.disj A D) B)
    (comp (dist B A D) (tensor .disj (swap .conj B A) (id D)))

def finish (T B A : NormalForm P) : Hom (.conj (.conj T B) A) (.conj T (.conj A B)) :=
  comp (assocL .conj T B A) (tensor .conj (id T) (swap .conj B A))

def stepWithContext (T A D B : NormalForm P) :
    Hom (.conj T (.conj (.disj A D) B)) (.disj (.conj T (.conj A B)) D) :=
  comp (tensor .conj (id T) (swap .conj (.disj A D) B))
    (comp (assocR .conj T B (.disj A D))
      (comp (dist (.conj T B) A D) (tensor .disj (finish T B A) (id D))))

theorem step_strength (T A D B : NormalForm P) :
    comp (tensor .conj (id T) (step A D B)) (dist T (.conj A B) D) =
      stepWithContext T A D B := by
  unfold step stepWithContext
  rw [tensor_factor .conj (id T) (swap .conj (.disj A D) B),
    tensor_factor .conj (id T) (dist B A D)]
  simp only [Laws.assoc]
  rw [← Laws.dist_nat]
  rw [← Laws.assoc (tensor .conj (id T) (dist B A D)), conjunction]
  simp only [Laws.assoc]
  rw [Laws.tensor_comp, Laws.id_comp]
  rfl

/-- Sequential distribution, with the A and B copies kept in their tagged order. -/
def sequential (T A D B : NormalForm P) :
    Hom (.conj (.conj T (.disj A D)) B) (.disj (.conj T (.conj A B)) D) :=
  comp (assocL .conj T (.disj A D) B) (stepWithContext T A D B)

/-- The distribution square in the principal conjunction-cut equation. -/
theorem mixed_strength (T A D B E : NormalForm P) :
    comp (tensor .conj (id T) (mixedDisj A D B E))
        (dist T (.conj A B) (.disj D E)) =
      comp (assocR .conj T (.disj A D) (.disj B E))
        (comp (dist (.conj T (.disj A D)) B E)
          (comp (tensor .disj (sequential T A D B) (id E))
            (assocL .disj (.conj T (.conj A B)) D E))) := by
  have hm : mixedDisj A D B E =
      comp (dist (.disj A D) B E)
        (comp (tensor .disj (step A D B) (id E)) (assocL .disj (.conj A B) D E)) := rfl
  rw [hm, tensor_factor .conj (id T) (dist (.disj A D) B E),
    tensor_factor .conj (id T) (tensor .disj (step A D B) (id E))]
  simp only [Laws.assoc]
  rw [disjunction]
  rw [← Laws.assoc (tensor .conj (id T) (tensor .disj (step A D B) (id E))),
    ← Laws.dist_nat]
  simp only [Laws.assoc]
  rw [← Laws.assoc (tensor .conj (id T) (dist (.disj A D) B E)), conjunction]
  simp only [Laws.assoc]
  rw [← Laws.assoc (tensor .disj (assocL .conj T (.disj A D) B) (id E)),
    Laws.tensor_comp, Laws.id_comp]
  rw [← Laws.assoc (tensor .disj
      (comp (assocL .conj T (.disj A D) B) (tensor .conj (id T) (step A D B))) (id E)),
    Laws.tensor_comp, Laws.id_comp]
  rw [Laws.assoc, step_strength]
  rfl

end CutDistribution
end DosenPetric.Reduced.Gentzen.MirrorCalculus
