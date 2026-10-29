module

public import DosenPetric.PresentationShortQ

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Presentation.ShortProof
universe u
variable {P : Type u}

theorem toTop_pre {A B : Formula P} (f : Hom A B) : comp f (toTop B) = toTop A :=
  (operations P).toTop_unique _

/-- The relevant witnessed zero is the arrow through the terminal object. -/
theorem context_zero_through_top (A : Formula P) :
    (zeroIdentity P).zeroOf (comp (fst A .bot) (inl A .top)) =
      comp (toTop (.conj A .bot)) (inr A .top) :=
  ((interpretation P).through_top (toTop (.conj A .bot)) (inr A .top)
    (comp (fst A .bot) (inl A .top))).symm

theorem q_zero_form (A : Formula P) :
    copair ((zeroIdentity P).zeroOf (comp (fst A .bot) (inl A .top))) (inr A .top) =
      comp (toTop (.disj (.conj A .bot) .top)) (inr A .top) := by
  apply coherence
  have hz : occurrenceMap ((zeroIdentity P).zeroOf (comp (fst A .bot) (inl A .top))) = Relations.empty :=
    (interpretation P).map_zeroOf (comp (fst A .bot) (inl A .top))
  rw [occurrence_copair,hz,
    occurrence_comp,occurrence_toTop,Relations.empty_comp]
  funext x y
  cases x with | inl x => rfl | inr x => cases x

variable (Q : Congruence (operations P))
variable (allK : ∀ A, ContextualCollapse.K Q (Z := zeroIdentity P) A)
include allK

theorem q_terminal (A : Formula P) :
    Q.Rel (q A) (comp (toTop (.disj (.conj A .bot) .top)) (inr A .top)) := by
  have hh := Q.copair (allK A) (Q.refl (inr A .top))
  change Q.Rel (q A)
    (copair ((zeroIdentity P).zeroOf (comp (fst A .bot) (inl A .top))) (inr A .top)) at hh
  rw [q_zero_form] at hh
  exact hh

/-- q_A's original inverse makes the terminal summand a retraction modulo Q. -/
theorem terminal_id (A : Formula P) :
    Q.Rel (id (.disj A .top)) (comp (toTop (.disj A .top)) (inr A .top)) := by
  have hh := Q.pre (qInverse A) (q_terminal Q allK A)
  change Q.Rel (comp (qInverse A) (q A))
    (comp (qInverse A) (comp (toTop (.disj (.conj A .bot) .top)) (inr A .top))) at hh
  rw [qInverse_q,← Laws.assoc,toTop_pre] at hh
  exact hh

theorem terminal_hom (A X : Formula P) (f : Hom X (.disj A .top)) :
    Q.Rel f (comp (toTop X) (inr A .top)) := by
  have hh := Q.pre f (terminal_id Q allK A)
  change Q.Rel (comp f (id (.disj A .top)))
    (comp f (comp (toTop (.disj A .top)) (inr A .top))) at hh
  rw [Laws.comp_id,← Laws.assoc,toTop_pre] at hh
  exact hh

theorem terminal_pair (A X : Formula P) (f g : Hom X (.disj A .top)) : Q.Rel f g :=
  Q.trans (terminal_hom Q allK A X f) (Q.symm (terminal_hom Q allK A X g))

end DosenPetric.Presentation.ShortProof
