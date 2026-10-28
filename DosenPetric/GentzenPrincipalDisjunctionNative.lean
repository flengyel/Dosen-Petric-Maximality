module

public import DosenPetric.GentzenPrincipalDisjunction
public import DosenPetric.GentzenSideProductCalculations

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace PrincipalDisjunction

variable {V A B T D E X Y : NormalForm P}

/-- The binary disjunction input before its context-fold comparisons. -/
def binaryInput (g : Hom (.conj A D) X) (h : Hom (.conj B E) Y) :
    Hom (.conj (.disj A B) (.conj D E)) (.disj X Y) :=
  comp (swap .conj (.disj A B) (.conj D E))
    (comp (ofTerm (Rules.sourceConj D E A B))
      (tensor .disj (comp (swap .conj D A) g) (comp (swap .conj E B) h)))

/-- Swap the first two disjunction slots while preserving their trailing context. -/
def frontTwo (A B T : NormalForm P) : Hom (.disj A (.disj B T)) (.disj B (.disj A T)) :=
  (sideM P .disj).cross B A T

def reflectionInput (f : Hom V (.disj A (.disj B T))) : Hom V (.disj (.disj T A) B) :=
  comp f (comp (assocR .disj A B T)
    (comp (swap .disj (.disj A B) T) (assocR .disj T A B)))

theorem reflection_left (f : Hom V (.disj A (.disj B T))) :
    comp (comp (reflectionInput f) (assocL .disj T A B)) (swap .disj T (.disj A B)) =
      comp f (assocR .disj A B T) := by
  simp only [reflectionInput, Laws.assoc]
  rw [← Laws.assoc (assocR .disj T A B), Laws.assocR_L, Laws.id_comp,
    Laws.swap_swap, Laws.comp_id]

theorem reflection_inner (f : Hom V (.disj A (.disj B T))) :
    comp (reflectionInput f) (swap .disj (.disj T A) B) =
      comp (comp f (frontTwo A B T)) (tensor .disj (id B) (swap .disj A T)) := by
  have he := (sideD P .disj).dual_inner_route (side_unit .disj) (side_swap_snd .disj) A B T
  dsimp only [frontTwo, MonoidalData.cross, side, category, opposite, sideM, disjMonoidal] at he ⊢
  simpa only [reflectionInput, Laws.assoc] using congrArg (fun k => comp f k) he

theorem reflection_outer (X A T : NormalForm P) :
    comp (tensor .disj (id X) (swap .disj A T))
      (comp (assocR .disj X T A) (swap .disj (.disj X T) A)) = frontTwo X A T := by
  have he := (sideD P .disj).dual_outer_route (side_unit .disj) (side_swap_snd .disj) X A T
  dsimp only [frontTwo, MonoidalData.cross, side, category, opposite, sideM, disjMonoidal] at he ⊢
  simpa only [Laws.assoc] using he

theorem reflected_inner (f : Hom V (.disj A (.disj B T))) (h : Hom (.conj B E) Y) :
    reflectedSplice (comp (swap .conj E B) h) (reflectionInput f) =
      comp (splice (comp f (frontTwo A B T)) h) (tensor .disj (id Y) (swap .disj A T)) := by
  unfold reflectedSplice
  rw [← Laws.assoc (swap .conj B E), Laws.swap_swap, Laws.id_comp, reflection_inner,
    Splice.residual]

/-- The native principal disjunction cut equals two component-formula splices. -/
theorem equation (f : Hom V (.disj A (.disj B T)))
    (g : Hom (.conj A D) X) (h : Hom (.conj B E) Y) :
    splice (comp f (assocR .disj A B T)) (binaryInput g h) =
      comp (assocL .conj D E V)
        (comp (splice (comp (splice (comp f (frontTwo A B T)) h) (frontTwo Y A T)) g)
          (assocR .disj X Y T)) := by
  have he := reflected_equation (comp (swap .conj E B) h)
    (comp (swap .conj D A) g) (reflectionInput f)
  have hl : reflectedSplice
      (comp (ofTerm (Rules.sourceConj D E A B))
        (tensor .disj (comp (swap .conj D A) g) (comp (swap .conj E B) h)))
      (comp (reflectionInput f) (assocL .disj T A B)) =
      splice (comp f (assocR .disj A B T)) (binaryInput g h) := by
    unfold reflectedSplice
    rw [reflection_left]
    rfl
  rw [hl, reflected_inner] at he
  unfold reflectedSplice at he
  rw [← Laws.assoc (swap .conj A D), Laws.swap_swap, Laws.id_comp] at he
  simp only [Laws.assoc] at he
  rw [reflection_outer] at he
  exact he

end PrincipalDisjunction
end DosenPetric.Reduced.Gentzen
