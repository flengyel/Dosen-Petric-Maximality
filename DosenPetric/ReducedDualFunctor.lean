module

public import DosenPetric.ReducedDualRelations

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced
universe u
variable {P : Type u}
open NormalForm

/-- Reflection preserves quotient equality by the proved converse-relation law. -/
theorem dual_of_eq {A B : NormalForm P} {f g : Term P A B} (h : ofTerm f = ofTerm g) :
    ofTerm f.dual = ofTerm g.dual := by
  apply faithful
  funext x y
  apply propext
  have hf := Term.dual_relation f (fromDual A y) (fromDual B x)
  have hg := Term.dual_relation g (fromDual A y) (fromDual B x)
  rw [to_fromDual,to_fromDual] at hf hg
  have he := congrArg (fun r => occurrenceMap r (fromDual A y) (fromDual B x)) h
  exact hf.trans ((Iff.of_eq he).trans hg.symm)

/-- The actual contravariant reflection on reduced quotient arrows. -/
def dualHom {A B : NormalForm P} (f : Hom A B) : Hom B.dual A.dual :=
  Quotient.liftOn f (fun t => ofTerm t.dual) (fun _ _ h => dual_of_eq (sound h))

theorem dualHom_ofTerm {A B : NormalForm P} (f : Term P A B) :
    dualHom (ofTerm f) = ofTerm f.dual := rfl

theorem dualHom_id (A : NormalForm P) : dualHom (id A) = id A.dual := rfl

theorem dualHom_comp {A B C : NormalForm P} (f : Hom A B) (g : Hom B C) :
    dualHom (comp f g) = comp (dualHom g) (dualHom f) := by
  induction f using Quotient.inductionOn with | h f =>
  induction g using Quotient.inductionOn with | h g => rfl

theorem dualHom_relation {A B : NormalForm P} (f : Hom A B)
    (x : A.formula.Occ) (y : B.formula.Occ) :
    occurrenceMap (dualHom f) (toDual B y) (toDual A x) ↔ occurrenceMap f x y := by
  induction f using Quotient.inductionOn with | h f => exact Term.dual_relation f x y

def dualFunctor (P : Type u) : Functor (opposite (category P)) (category P) where
  obj := NormalForm.dual
  map := dualHom
  map_id := dualHom_id
  map_comp f g := dualHom_comp g f

end DosenPetric.Reduced
