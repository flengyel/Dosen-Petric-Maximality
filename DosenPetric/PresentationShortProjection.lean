module

public import DosenPetric.PresentationShortE
public import DosenPetric.PresentationShortTerminal

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Presentation.ShortProof
universe u
variable {P : Type u}

theorem pair_fst {X A B : Formula P} (f : Hom X A) (g : Hom X B) :
    comp (pair f g) (fst A B) = f := (operations P).pair_fst f g

theorem pair_snd {X A B : Formula P} (f : Hom X A) (g : Hom X B) :
    comp (pair f g) (snd A B) = g := (operations P).pair_snd f g

theorem pair_eta {X A B : Formula P} (f : Hom X (.conj A B)) :
    pair (comp f (fst A B)) (comp f (snd A B)) = f := (operations P).pair_eta f

def r (A : Formula P) : Hom (.conj A (.disj A .top)) A := fst A (.disj A .top)
def i (A : Formula P) : Hom A (.conj A (.disj A .top)) :=
  pair (id A) (comp (toTop A) (inr A .top))

theorem i_r (A : Formula P) : comp (i A) (r A) = id A := pair_fst _ _

theorem e_r (A : Formula P) : comp (e A) (r A) = fst A A := by
  rw [e_definition]
  change comp (tensor .conj (id A) (inl A .top)) (fst A (.disj A .top)) = fst A A
  rw [← Laws.fst_nat,Laws.comp_id]

variable (Q : Congruence (operations P))

theorem pair_ext {X A B : Formula P} {f g : Hom X (.conj A B)}
    (h₁ : Q.Rel (comp f (fst A B)) (comp g (fst A B)))
    (h₂ : Q.Rel (comp f (snd A B)) (comp g (snd A B))) : Q.Rel f g := by
  have hh := Q.pair h₁ h₂
  change Q.Rel (pair (comp f (fst A B)) (comp f (snd A B)))
    (pair (comp g (fst A B)) (comp g (snd A B))) at hh
  rw [pair_eta,pair_eta] at hh
  exact hh

variable (allK : ∀ A, ContextualCollapse.K Q (Z := zeroIdentity P) A)
include allK

/-- The projection r is invertible modulo Q, by quotient-terminal uniqueness. -/
theorem r_i (A : Formula P) : Q.Rel (comp (r A) (i A)) (id _) := by
  apply pair_ext Q
  · apply Q.of_eq
    change comp (comp (r A) (pair (id A) (comp (toTop A) (inr A .top)))) (fst A (.disj A .top)) =
      comp (id _) (fst A (.disj A .top))
    rw [Laws.assoc,pair_fst,Laws.comp_id,Laws.id_comp]
    rfl
  · exact terminal_pair Q allK A (.conj A (.disj A .top)) _ _

def u (A : Formula P) : Hom A (.conj A A) := comp (i A) (eInverse A)

/-- Conjugate r's inverse equation by the particular original e_A isomorphism. -/
theorem projection_id (A : Formula P) :
    Q.Rel (id (.conj A A)) (comp (fst A A) (u A)) := by
  have hh := Q.post (Q.pre (e A) (r_i Q allK A)) (eInverse A)
  change Q.Rel (comp (comp (e A) (comp (r A) (i A))) (eInverse A))
    (comp (comp (e A) (id _)) (eInverse A)) at hh
  simp only [Laws.assoc,Laws.comp_id] at hh
  rw [← Laws.assoc (e A) (r A),e_r,e_eInverse] at hh
  exact Q.symm hh

theorem diagonal_u (A : Formula P) : Q.Rel (diag A) (u A) := by
  have hh := Q.pre (diag A) (projection_id Q allK A)
  change Q.Rel (comp (diag A) (id _)) (comp (diag A) (comp (fst A A) (u A))) at hh
  rw [Laws.comp_id,← Laws.assoc,Laws.diag_fst,Laws.id_comp] at hh
  exact hh

theorem projection_diagonal (A : Formula P) :
    Q.Rel (id (.conj A A)) (comp (fst A A) (diag A)) :=
  Q.trans (projection_id Q allK A) (Q.comp (Q.refl (fst A A)) (Q.symm (diagonal_u Q allK A)))

theorem projections (A : Formula P) : Q.Rel (snd A A) (fst A A) := by
  have hh := Q.post (projection_diagonal Q allK A) (snd A A)
  change Q.Rel (comp (id _) (snd A A)) (comp (comp (fst A A) (diag A)) (snd A A)) at hh
  rw [Laws.id_comp,Laws.assoc,Laws.diag_snd,Laws.comp_id] at hh
  exact hh

/-- The manuscript's short q/e collapse argument, directly modulo Q. -/
theorem total : Q.Total := by
  intro A B f g
  have hh := Q.pre (pair f g) (projections Q allK B)
  change Q.Rel (comp (pair f g) (snd B B)) (comp (pair f g) (fst B B)) at hh
  rw [pair_fst,pair_snd] at hh
  exact Q.symm hh

end DosenPetric.Presentation.ShortProof
