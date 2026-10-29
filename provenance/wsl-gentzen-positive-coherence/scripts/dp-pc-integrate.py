import re
base=root/'DosenPetric'
base_commit='75b8e48'
mods=sorted(p for p in base.glob('*.lean') if subprocess.run(['git','cat-file','-e',base_commit+':'+str(p.relative_to(root))],cwd=root,stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL).returncode)
assert len(mods)==18,len(mods)
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
open DosenPetric DosenPetric.Reduced DosenPetric.Reduced.Gentzen
namespace PositiveCoherenceChecks
example {P : Type u} : PositiveCoherence P := positive_coherence
example {P : Type u} : Faithful P := Reduced.faithful
example {P : Type u} : OccurrenceInterpretation (Presentation.operations P) (Presentation.zeroIdentity P) :=
  Presentation.interpretation P
example {P : Type u} : SignedLabelPreservation (Presentation.interpretation P) :=
  Presentation.interpretation_signedLabel P
example : (Presentation.operations Nat).fst (.var 0) (.var 0) ≠
    (Presentation.operations Nat).snd (.var 0) (.var 0) := Presentation.nonthin 0
example : ¬ Nonempty ((Presentation.category Empty).Hom .top .bot) := Presentation.empty_hom Empty
example {P : Type u} {A B : Formula P} (f g : Presentation.Hom A B)
    (h : Presentation.occurrenceMap f = Presentation.occurrenceMap g) : f = g := Presentation.coherence h
example : ofTerm (P:=Empty) (Term.id .top) = ofTerm (Term.zero .top) := by
  apply Reduced.faithful
  funext x y
  cases x
example : ofTerm (Term.id (P:=Nat) (.lit (.neg 0))) ≠ ofTerm (Term.zero (.lit (.neg 0))) := by
  intro h
  have hx : occurrenceMap (ofTerm (Term.id (P:=Nat) (.lit (.neg 0))))
      (Literal.neg 0).point (Literal.neg 0).point := rfl
  rw [h] at hx
  exact hx
'''
# Check every general theorem in the actual assembly at its exact declaration type.
for file,ns,name,call in [
 ('GentzenPositiveNormalization','','positive_cutFree_represented','t ht'),
 ('GentzenPureFormulas','','positive_mix_represented','t ht hA hB'),
 ('GentzenMixNormalForm','G','mix_normal_form','g hg'),
 ('GentzenPurePositiveCoherence','','pure_positive_coherence','f g hf hg hA hB h'),
 ('GentzenNormalFormCoherence','','normal_positive_coherence','d c f g hf hg h'),
 ('GentzenNormalExpansion','','dnf_expansion','A'),
 ('GentzenNormalExpansion','','cnf_expansion','A'),
 ('GentzenPositiveCoherence','','represented_coherence','f g hf hg h')]:
 s=(base/(file+'.lean')).read_text();m=re.search(r'^theorem '+name+r'\s([\s\S]*?) := by\n',s,re.M);assert m,name
 checks+='\nexample {P : Type u} '+m[1]+' :=\n  '+(ns+'.' if ns else '')+name+' '+call+'\n'
checks+='''
example {P : Type u} (l : Literal P) :
    (PurePort.left (.lit l) (PurePort.here l) : PurePort .conj (.conj (.lit l) (.lit l)) l).position ≠
    (PurePort.right (.lit l) (PurePort.here l) : PurePort .conj (.conj (.lit l) (.lit l)) l).position := by
  intro h
  simp only [PurePort.position] at h
  cases h
example {P : Type u} (l : Literal P) :
    occurrenceMap (PureEdge.arrow (P:=P) (A:=.lit l) (B:=.disj (.lit l) (.lit l))
      ⟨l,.here l,.left (.lit l) (.here l)⟩) l.point (Sum.inl l.point) := by
  rw [PureEdge.relation]
  exact ⟨rfl,rfl⟩
example (w : Hom (P:=Empty) .top .top) : finiteUnion w [] = zeroOf w := rfl
example (l : Literal Nat) :
    ∃ g : G Nat [.lit l] [.lit l], g.CutFree ∧ g.Atomized ∧
      ofTerm g.denote = comp (rightOut .conj (.lit l))
        (comp (ofTerm (Term.id (.lit l))) (rightIn .disj (.lit l))) ∧
      ∀ x y, g.relation (singletonOcc .conj (.lit l) x) (singletonOcc .disj (.lit l) y) ↔
        (Term.id (.lit l)).relation x y := positive_cutFree_represented _ (.id _)
end PositiveCoherenceChecks
'''
anchors=['DosenPetric.Reduced.Gentzen.positive_coherence','DosenPetric.Reduced.faithful','DosenPetric.Reduced.boolean_coherence','DosenPetric.Presentation.coherence','DosenPetric.Presentation.interpretation','DosenPetric.Presentation.interpretation_signedLabel','DosenPetric.Reduced.Gentzen.G.mix_normal_form','DosenPetric.Reduced.Gentzen.G.pure_cutFree_faithful','DosenPetric.Reduced.Gentzen.normal_positive_coherence','DosenPetric.Reduced.Gentzen.dnf_expansion','DosenPetric.Reduced.Gentzen.cnf_expansion','DosenPetric.Reduced.Gentzen.PureEdge.evaluate_faithful','DosenPetric.Reduced.finiteUnion.eq_of_members']
p=root/'Checks/Axioms.lean';s=p.read_text()
for a in anchors:
 line='#print axioms '+a+'\n'
 if line not in s:s+=line
 checks+='\n'+line
p.write_text(s);(root/'Checks/PositiveCoherence.lean').write_text(checks)
print('Integrated eighteen actual coherence modules and full intended-presentation checks')
