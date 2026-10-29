base_commit='b257325e04631d1f396fcd640070ae52741aba69'
mods=sorted(p for p in (root/'DosenPetric').glob('*.lean') if subprocess.run(['git','cat-file','-e',base_commit+':'+str(p.relative_to(root))],cwd=root,stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL).returncode)
assert len(mods)==12,len(mods)
p=root/'DosenPetric.lean';s=p.read_text()
for m in mods:
 line='public import DosenPetric.'+m.stem+'\n'
 if line not in s:s+=line
p.write_text(s)
checks='''module
import DosenPetric
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u v w w'
open DosenPetric
open PresentationSemantics
namespace FullSourceModelChecks
variable {X : Type u} {C : Category.{u,v} X} {O : Objects X} {S : Primitives C O}
  {P : Type w} {R : Type w'}
example (M : Model P S) (α : P → X) : Interpretation S P := S.canonicalInterpretation M.equations α
example (F : Interpretation S R) (σ : P → Formula R) : Interpretation S P := F.precompose σ
example (F : Interpretation S P) (M : Model P S) {A B : Formula P} (f : Presentation.Hom A B) :
    HEq (F.map f) (S.evaluateHom M.equations F.valuation f) := F.hom_evaluation M.equations f
example : Model P (Source.primitives R) := Source.model P R
example : Model Nat (Source.primitives Nat) := Source.model Nat Nat
example : Model Empty (Source.primitives Empty) := Source.model Empty Empty
example : ¬ Nonempty ((Presentation.category Nat).Hom .top .bot) := Presentation.empty_hom Nat
example : Presentation.id (.var 0 : Formula Nat) ≠ Presentation.zero (.var 0) := Presentation.identity_ne_primitive_zero 0
example : Presentation.ProofCongruence P := Agreement.congruence (S:=S) (P:=P)
example : (Agreement.congruence (S:=S) (P:=P)).Closed := Agreement.closed
example (M : Model P S) {A B : Formula P} (f g : Presentation.Hom A B) :
    Agreement S P f g ↔ ∀ α : P → X, S.evaluateHom M.equations α f = S.evaluateHom M.equations α g :=
  Agreement.iff_valuations M.equations f g
example [Nonempty P] (M : Model P S) {A B : Formula P} (f g : Presentation.Hom A B) (hne : f ≠ g)
    (h : ∀ α : P → X, S.evaluateHom M.equations α f = S.evaluateHom M.equations α g) :
    ∀ {Y Z : X} (a b : C.Hom Y Z), a = b := model_corollary M f g hne h
example [Nonempty P] (M : Model P S) {A B : Formula P} (f g : Presentation.Hom A B) (hne : f ≠ g)
    (h : Agreement S P f g) : ∀ {Y Z : X} (a b : C.Hom Y Z), a = b :=
  model_corollary_interpretations M f g hne h
end FullSourceModelChecks
'''
anchors=['DosenPetric.PresentationSemantics.'+n for n in ['Primitives.evaluate_derives','Primitives.evaluateHom','Primitives.evaluationFunctor','Primitives.canonicalInterpretation','Interpretation.precompose','Interpretation.object_evaluation','Interpretation.raw_evaluation','Interpretation.hom_evaluation','Source.equations','Source.bicartesian','Source.model','Agreement.fragment_closed','Agreement.congruence','Agreement.closed','Agreement.iff_valuations','model_corollary','model_corollary_interpretations']]+['DosenPetric.Presentation.'+n for n in ['fragment_maximality','fragment_dichotomy','ProofCongruence.of_closed_fragment']]
p=root/'Checks/Axioms.lean';s=p.read_text()
for a in anchors:
 line='#print axioms '+a+'\n'
 if line not in s:s+=line
 checks+='\n'+line
p.write_text(s);(root/'Checks/FullSourceModels.lean').write_text(checks)
print('Integrated twelve complete-source model modules and exact independent-universe public checks')
