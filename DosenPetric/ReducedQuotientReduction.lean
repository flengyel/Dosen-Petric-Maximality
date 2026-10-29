module

public import DosenPetric.PresentationCoherence

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced
universe u
variable {P : Type u}
open Presentation.NegationNormalization (normal)

/-- The proved faithfulness discharges preservation of generated source equality. -/
theorem red_derives {A B : Formula P} {f g : Presentation.Term P A B}
    (h : Presentation.Derives f g) : ofTerm (red f) = ofTerm (red g) := by
  apply faithful
  change (red f).relation = (red g).relation
  rw [occurrence_red,occurrence_red,Presentation.sound h]

/-- The signed-literal reduction now descends to actual quotient arrows. -/
def reduceHom {A B : Formula P} (f : Presentation.Hom A B) : Hom (normal A) (normal B) :=
  Quotient.liftOn f (fun t => ofTerm (red t)) (fun _ _ h => red_derives h)

theorem reduceHom_ofTerm {A B : Formula P} (f : Presentation.Term P A B) :
    reduceHom (Presentation.ofTerm f) = ofTerm (red f) := rfl

theorem reduceHom_id (A : Formula P) : reduceHom (Presentation.id A) = id (normal A) := rfl

theorem reduceHom_comp {A B C : Formula P} (f : Presentation.Hom A B) (g : Presentation.Hom B C) :
    reduceHom (Presentation.comp f g) = comp (reduceHom f) (reduceHom g) := by
  induction f using Quotient.inductionOn with | h f =>
  induction g using Quotient.inductionOn with | h g => rfl

theorem reduceHom_tensor_conj {A B C D : Formula P}
    (f : Presentation.Hom A C) (g : Presentation.Hom B D) :
    reduceHom (Presentation.tensor .conj f g) = tensor .conj (reduceHom f) (reduceHom g) := by
  induction f using Quotient.inductionOn with | h f =>
  induction g using Quotient.inductionOn with | h g => rfl

theorem reduceHom_tensor_disj {A B C D : Formula P}
    (f : Presentation.Hom A C) (g : Presentation.Hom B D) :
    reduceHom (Presentation.tensor .disj f g) = tensor .disj (reduceHom f) (reduceHom g) := by
  induction f using Quotient.inductionOn with | h f =>
  induction g using Quotient.inductionOn with | h g => rfl

theorem inclusion_reduceHom {A B : Formula P} (f : Presentation.Hom A B) :
    inclusion (reduceHom f) = (Presentation.normalization P).transport f := by
  induction f using Quotient.inductionOn with | h f => exact red_sound f

theorem reduceHom_occurrence {A B : Formula P} (f : Presentation.Hom A B) :
    occurrenceMap (reduceHom f) = Presentation.occurrenceMap ((Presentation.normalization P).transport f) := by
  induction f using Quotient.inductionOn with | h f => exact occurrence_red f

theorem inclusion_injective {A B : NormalForm P} {f g : Hom A B}
    (h : inclusion f = inclusion g) : f = g := by
  apply faithful
  rw [occurrence_inclusion,occurrence_inclusion,h]

theorem reduceHom_injective {A B : Formula P} {f g : Presentation.Hom A B}
    (h : reduceHom f = reduceHom g) : f = g := by
  apply (Presentation.normalization P).transport_injective
  rw [← inclusion_reduceHom,← inclusion_reduceHom,h]

end DosenPetric.Reduced
