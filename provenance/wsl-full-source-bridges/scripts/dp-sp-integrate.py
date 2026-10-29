import re
base_commit='a80a353993668d716194d0f5a80744edc8aaae7f'
base=root/'DosenPetric'
mods=sorted(p for p in base.glob('*.lean') if subprocess.run(['git','cat-file','-e',base_commit+':'+str(p.relative_to(root))],cwd=root,stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL).returncode)
p=root/'DosenPetric.lean';s=p.read_text()
for m in mods:
 line='public import DosenPetric.'+m.stem+'\n'
 if line not in s:s+=line
p.write_text(s)
checks='''module
import DosenPetric
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open DosenPetric
namespace SourceMaximalityChecks
example (P : Type u) : Functor (Presentation.category P) (Reduced.category P) := Reduced.reductionFunctor P
example (P : Type u) : Functor (Reduced.category P) (Presentation.category P) := Reduced.inclusionFunctor P
example (P : Type u) : NaturalIsomorphism (Functor.identity (Presentation.category P))
    ((Reduced.reductionFunctor P).comp (Reduced.inclusionFunctor P)) := Reduced.normalizationNaturalIso P
example (P : Type u) : Functor (opposite (Presentation.category P)) (Presentation.category P) := Presentation.negationFunctor P
example (P : Type u) : NaturalIsomorphism (Presentation.doubleNegationFunctor P)
    (Functor.identity (Presentation.category P)) := Presentation.doubleNegationNaturalIso P
example {P : Type u} {A B : Formula P} (f : Presentation.Term P A B) :
    Presentation.Term P (.neg B) (.neg A) := f.negate
example {P : Type u} (Q : Presentation.ProofCongruence P) (h : Q.Closed)
    {A B : Formula P} (f g : Presentation.Hom A B) (hne : f ≠ g) (hf : Q.Rel f g) : Q.Total :=
  Presentation.maximality Q h f g hne hf
example {P : Type u} (Q : Presentation.ProofCongruence P) (h : Q.Closed) :
    (∀ {A B} (f g : Presentation.Hom A B), Q.Rel f g ↔ f = g) ∨ Q.Total :=
  Presentation.congruence_dichotomy Q h
example {P : Type u} (Q : Presentation.RawProofCongruence P) (h : Q.Closed)
    {A B : Formula P} (f g : Presentation.Term P A B) (hne : ¬ Presentation.Derives f g) (hf : Q.Rel f g) :
    ∀ {C D} (k l : Presentation.Term P C D), Q.Rel k l := Presentation.raw_maximality Q h f g hne hf
example : Presentation.Hom (.neg (.conj (.var 0) (.var 0) : Formula Nat)) (.neg (.var 0)) :=
  Presentation.negate (Presentation.diag (.var 0))
example : Presentation.Hom (.neg (.top : Formula Empty)) (.neg .top) := Presentation.negate (Presentation.id .top)
example : ¬ Nonempty ((Presentation.category Empty).Hom .top .bot) := Presentation.empty_hom Empty
example : (Presentation.operations Nat).fst (.var 0) (.var 0) ≠
    (Presentation.operations Nat).snd (.var 0) (.var 0) := Presentation.nonthin 0
'''
# Exact types from source, independent use sites with no weakened hypotheses.
items=[
('ReducedQuotientReduction','DosenPetric.Reduced','reduceHom_injective','h'),
('ReducedReductionFunctor','DosenPetric.Reduced','reduction_inclusion','f'),
('ReducedRecovery','DosenPetric.Reduced','recover_reduceHom','f'),
('ReducedRecovery','DosenPetric.Reduced','reduce_recoverHom','f'),
('ReducedDualFunctor','DosenPetric.Reduced','dualHom_relation','f x y'),
('ReducedDualInvolution','DosenPetric.Reduced','dualHom_involutive','f'),
('ReducedNegationLaws','DosenPetric.Reduced','negReduceHom_twice','f'),
('PresentationNegationNaturality','DosenPetric.Presentation','dnOut_natural','f'),
('PresentationNegationNaturality','DosenPetric.Presentation','dnIn_natural','f'),
('PresentationNegationNaturality','DosenPetric.Presentation','dmConjOut_natural','f g'),
('PresentationNegationNaturality','DosenPetric.Presentation','dmConjIn_natural','f g'),
('PresentationNegationNaturality','DosenPetric.Presentation','dmDisjOut_natural','f g'),
('PresentationNegationNaturality','DosenPetric.Presentation','dmDisjIn_natural','f g'),
('PresentationNormalizationTerms','DosenPetric.Presentation.NegationNormalization','forwardTerm_denotes','A s'),
('PresentationNormalizationTerms','DosenPetric.Presentation.NegationNormalization','backwardTerm_denotes','A s'),
('PresentationNegationTerms','DosenPetric.Presentation','negateTerm_denotes','f'),
('PresentationNegationTerms','DosenPetric.Presentation','negate_derives','h'),
('PresentationNegationCoordinates','DosenPetric.Presentation.NegationNormalization','toOcc_neg','A x'),
('PresentationNegationOccurrence','DosenPetric.Presentation','occurrence_negate','f x y')]
anchors=[]
for file,ns,name,call in items:
 s=(base/(file+'.lean')).read_text();m=re.search(r'^theorem '+name+r'\s([\s\S]*?) :=(?: by)?\n',s,re.M);assert m,name
 checks+='\nsection\nopen '+ns+'\nopen DosenPetric.Presentation.NegationNormalization (normal)\nopen DosenPetric.NormalForm (toDual castOcc)\n'+('open DosenPetric.Presentation\n' if ns.endswith('.NegationNormalization') else '')+'example {P : Type u} '+m[1]+' := '+name+' '+call+'\nend\n'
 anchors.append(ns+'.'+name)
checks+='''
example {P : Type u} (Q : Presentation.RawProofCongruence P) {A B : Formula P}
    (f g : Presentation.Term P A B) : Q.toQuotient.toRaw.Rel f g ↔ Q.Rel f g := Q.quotient_raw_rel f g
example {P : Type u} (Q : Presentation.ProofCongruence P) {A B : Formula P}
    (f g : Presentation.Hom A B) : Q.toRaw.toQuotient.Rel f g ↔ Q.Rel f g := Q.raw_quotient_rel f g
example {P : Type u} (Q : Presentation.RawProofCongruence P) (h : Q.Closed) : Q.toQuotient.Closed := Q.toQuotient_closed h
example {P : Type u} (Q : Presentation.ProofCongruence P) (h : Q.Closed) : Q.toRaw.Closed := Q.toRaw_closed h
example {P : Type u} (Q : Presentation.ProofCongruence P) (h : Q.Closed) :
    (Presentation.substitution P).Closed Q.fragment := Q.fragment_closed h
end SourceMaximalityChecks
'''
anchors += ['DosenPetric.Presentation.maximality','DosenPetric.Presentation.congruence_dichotomy','DosenPetric.Presentation.raw_maximality','DosenPetric.Presentation.RawProofCongruence.toQuotient','DosenPetric.Presentation.ProofCongruence.toRaw','DosenPetric.Presentation.ProofCongruence.raw_quotient_rel','DosenPetric.Presentation.RawProofCongruence.quotient_raw_rel']
p=root/'Checks/Axioms.lean';s=p.read_text()
for a in anchors:
 line='#print axioms '+a+'\n'
 if line not in s:s+=line
 checks+='\n'+line
p.write_text(s);(root/'Checks/SourceMaximality.lean').write_text(checks)
print('Integrated',len(mods),'source bridge modules and exact source-category checks')
