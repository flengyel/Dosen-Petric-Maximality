base_commit='d68da50'
mods=sorted(p for p in (root/'DosenPetric').glob('*.lean') if subprocess.run(['git','cat-file','-e',base_commit+':'+str(p.relative_to(root))],cwd=root,stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL).returncode)
assert len(mods)==6,len(mods)
p=root/'DosenPetric.lean';s=p.read_text()
for m in mods:
 line='public import DosenPetric.'+m.stem+'\n'
 if line not in s:s+=line
p.write_text(s)
checks='''module
import DosenPetric
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u v
open DosenPetric DosenPetric.Presentation DosenPetric.Presentation.ShortProof
namespace ShortProofChecks
example {P : Type u} (A : Formula P) :
    q A = copair (comp (fst A .bot) (inl A .top)) (inr A .top) := q_definition A
example {P : Type u} (A : Formula P) : e A = tensor .conj (id A) (inl A .top) := e_definition A
example {P : Type u} (A : Formula P) : comp (q A) (qInverse A) = id _ := q_qInverse A
example {P : Type u} (A : Formula P) : comp (qInverse A) (q A) = id _ := qInverse_q A
example {P : Type u} (A : Formula P) : comp (e A) (eInverse A) = id _ := e_eInverse A
example {P : Type u} (A : Formula P) : comp (eInverse A) (e A) = id _ := eInverse_e A
example {P : Type u} (A : Formula P) : comp (e A) (ShortProof.r A) = fst A A := e_r A
example {P : Type u} (A : Formula P) : comp (ShortProof.i A) (ShortProof.r A) = id A := i_r A
example {P : Type u} (A : Formula P) :
    (zeroIdentity P).zeroOf (comp (fst A .bot) (inl A .top)) =
      comp (toTop (.conj A .bot)) (inr A .top) := context_zero_through_top A
section
variable {P : Type u} (Q : Congruence (operations P))
variable (allK : ∀ A, ContextualCollapse.K Q (Z := zeroIdentity P) A)
example (A : Formula P) : Q.Rel (q A) (comp (toTop (.disj (.conj A .bot) .top)) (inr A .top)) := q_terminal Q allK A
example (A : Formula P) : Q.Rel (id (.disj A .top)) (comp (toTop (.disj A .top)) (inr A .top)) := terminal_id Q allK A
example (A X : Formula P) (f g : Hom X (.disj A .top)) : Q.Rel f g := terminal_pair Q allK A X f g
example (A : Formula P) : Q.Rel (comp (ShortProof.r A) (ShortProof.i A)) (id _) := r_i Q allK A
example (A : Formula P) : Q.Rel (id (.conj A A)) (comp (fst A A) (ShortProof.u A)) := projection_id Q allK A
example (A : Formula P) : Q.Rel (diag A) (ShortProof.u A) := diagonal_u Q allK A
example (A : Formula P) : Q.Rel (id (.conj A A)) (comp (fst A A) (diag A)) := projection_diagonal Q allK A
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
example : comp (q (Formula.top : Formula Empty)) (qInverse .top) = id _ := q_qInverse _
example : comp (eInverse (Formula.bot : Formula Empty)) (e .bot) = id _ := eInverse_e _
example : comp (e (.conj (.neg (.var 0)) (.neg (.var 0)) : Formula Nat)) (eInverse _) = id _ := e_eInverse _
example : ¬ Nonempty ((category Empty).Hom .top .bot) := empty_hom Empty
end ShortProofChecks
'''
anchors=['DosenPetric.Presentation.short_maximality']+['DosenPetric.Presentation.ShortProof.'+x for x in ['q_qInverse','qInverse_q','e_eInverse','eInverse_e','context_zero_through_top','q_terminal','terminal_id','terminal_pair','e_r','i_r','r_i','projection_id','diagonal_u','projection_diagonal','projections','total','qTerm_subst','qInverseTerm_subst','eTerm_subst','eInverseTerm_subst','q_substitute','qInverse_substitute','e_substitute','eInverse_substitute']]
p=root/'Checks/Axioms.lean';s=p.read_text()
for a in anchors:
 line='#print axioms '+a+'\n'
 if line not in s:s+=line
 checks+='\n'+line
import re
checks=re.sub(r'\bid\b','Presentation.id',checks)
p.write_text(s);(root/'Checks/ShortProof.lean').write_text(checks)
print('Integrated six particular q/e proof modules and exact actual-main/substitution checks')
