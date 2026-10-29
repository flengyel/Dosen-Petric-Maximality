module
import DosenPetric
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u v
open DosenPetric DosenPetric.Presentation DosenPetric.Presentation.ShortProof
namespace ShortProofChecks
example {P : Type u} (A : Formula P) :
    q A = copair (comp (fst A .bot) (inl A .top)) (inr A .top) := q_definition A
example {P : Type u} (A : Formula P) : e A = tensor .conj (Presentation.id A) (inl A .top) := e_definition A
example {P : Type u} (A : Formula P) : comp (q A) (qInverse A) = Presentation.id _ := q_qInverse A
example {P : Type u} (A : Formula P) : comp (qInverse A) (q A) = Presentation.id _ := qInverse_q A
example {P : Type u} (A : Formula P) : comp (e A) (eInverse A) = Presentation.id _ := e_eInverse A
example {P : Type u} (A : Formula P) : comp (eInverse A) (e A) = Presentation.id _ := eInverse_e A
example {P : Type u} (A : Formula P) : comp (e A) (ShortProof.r A) = fst A A := e_r A
example {P : Type u} (A : Formula P) : comp (ShortProof.i A) (ShortProof.r A) = Presentation.id A := i_r A
example {P : Type u} (A : Formula P) :
    (zeroIdentity P).zeroOf (comp (fst A .bot) (inl A .top)) =
      comp (toTop (.conj A .bot)) (inr A .top) := context_zero_through_top A
section
variable {P : Type u} (Q : Congruence (operations P))
variable (allK : ∀ A, ContextualCollapse.K Q (Z := zeroIdentity P) A)
example (A : Formula P) : Q.Rel (q A) (comp (toTop (.disj (.conj A .bot) .top)) (inr A .top)) := q_terminal Q allK A
example (A : Formula P) : Q.Rel (Presentation.id (.disj A .top)) (comp (toTop (.disj A .top)) (inr A .top)) := terminal_id Q allK A
example (A X : Formula P) (f g : Hom X (.disj A .top)) : Q.Rel f g := terminal_pair Q allK A X f g
example (A : Formula P) : Q.Rel (comp (ShortProof.r A) (ShortProof.i A)) (Presentation.id _) := r_i Q allK A
example (A : Formula P) : Q.Rel (Presentation.id (.conj A A)) (comp (fst A A) (ShortProof.u A)) := projection_id Q allK A
example (A : Formula P) : Q.Rel (diag A) (ShortProof.u A) := diagonal_u Q allK A
example (A : Formula P) : Q.Rel (Presentation.id (.conj A A)) (comp (fst A A) (diag A)) := projection_diagonal Q allK A
example (A : Formula P) : Q.Rel (snd A A) (fst A A) := projections Q allK A
example : Q.Total := ShortProof.total Q allK
end
example {P : Type u} (Q : ProofCongruence P) (closed : Q.Closed)
    {A B : Formula P} (f g : Hom A B) (hne : f ≠ g) (hf : Q.Rel f g) : Q.Total := short_maximality Q closed f g hne hf
section
variable {P : Type u} {R : Type v} (σ : P → Formula R) (A : Formula P)
example : (qTerm A).subst σ = qTerm (A.subst σ) := qTerm_subst σ A
example : (qInverseTerm A).subst σ = qInverseTerm (A.subst σ) := qInverseTerm_subst σ A
example : (eTerm A).subst σ = eTerm (A.subst σ) := eTerm_subst σ A
example : (eInverseTerm A).subst σ = eInverseTerm (A.subst σ) := eInverseTerm_subst σ A
example : substitute σ (q A) = q (A.subst σ) := q_substitute σ A
example : substitute σ (qInverse A) = qInverse (A.subst σ) := qInverse_substitute σ A
example : substitute σ (e A) = e (A.subst σ) := e_substitute σ A
example : substitute σ (eInverse A) = eInverse (A.subst σ) := eInverse_substitute σ A
end
example : comp (q (Formula.top : Formula Empty)) (qInverse .top) = Presentation.id _ := q_qInverse _
example : comp (eInverse (Formula.bot : Formula Empty)) (e .bot) = Presentation.id _ := eInverse_e _
example : comp (e (.conj (.neg (.var 0)) (.neg (.var 0)) : Formula Nat)) (eInverse _) = Presentation.id _ := e_eInverse _
example : ¬ Nonempty ((category Empty).Hom .top .bot) := empty_hom Empty
end ShortProofChecks

#print axioms DosenPetric.Presentation.short_maximality

#print axioms DosenPetric.Presentation.ShortProof.q_qInverse

#print axioms DosenPetric.Presentation.ShortProof.qInverse_q

#print axioms DosenPetric.Presentation.ShortProof.e_eInverse

#print axioms DosenPetric.Presentation.ShortProof.eInverse_e

#print axioms DosenPetric.Presentation.ShortProof.context_zero_through_top

#print axioms DosenPetric.Presentation.ShortProof.q_terminal

#print axioms DosenPetric.Presentation.ShortProof.terminal_id

#print axioms DosenPetric.Presentation.ShortProof.terminal_pair

#print axioms DosenPetric.Presentation.ShortProof.e_r

#print axioms DosenPetric.Presentation.ShortProof.i_r

#print axioms DosenPetric.Presentation.ShortProof.r_i

#print axioms DosenPetric.Presentation.ShortProof.projection_id

#print axioms DosenPetric.Presentation.ShortProof.diagonal_u

#print axioms DosenPetric.Presentation.ShortProof.projection_diagonal

#print axioms DosenPetric.Presentation.ShortProof.projections

#print axioms DosenPetric.Presentation.ShortProof.total

#print axioms DosenPetric.Presentation.ShortProof.qTerm_subst

#print axioms DosenPetric.Presentation.ShortProof.qInverseTerm_subst

#print axioms DosenPetric.Presentation.ShortProof.eTerm_subst

#print axioms DosenPetric.Presentation.ShortProof.eInverseTerm_subst

#print axioms DosenPetric.Presentation.ShortProof.q_substitute

#print axioms DosenPetric.Presentation.ShortProof.qInverse_substitute

#print axioms DosenPetric.Presentation.ShortProof.e_substitute

#print axioms DosenPetric.Presentation.ShortProof.eInverse_substitute
