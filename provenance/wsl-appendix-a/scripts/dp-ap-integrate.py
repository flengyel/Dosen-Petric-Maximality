base_commit='37cce28d266bf9473e543ff26b3411ac71938ef1'
mods=sorted(p for p in (root/'DosenPetric').glob('*.lean') if subprocess.run(['git','cat-file','-e',base_commit+':'+str(p.relative_to(root))],cwd=root,stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL).returncode)
assert len(mods)==22,len(mods)
p=root/'DosenPetric.lean';s=p.read_text()
for m in mods:
 line='public import DosenPetric.'+m.stem+'\n'
 if line not in s:s+=line
p.write_text(s)
checks='''module
import DosenPetric
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u v w
open DosenPetric
namespace CompletePaperChecks
example {P : Type u} : Functor (Presentation.category P) FiniteSet.relationCategory := Presentation.finiteOccurrenceFunctor P
example {P : Type u} (A : Formula P) (x : A.Occ) : A.occurrenceAt (A.occurrenceIndex x) = x := A.occurrenceAt_index x
example {P : Type u} (A : Formula P) : Formula.fromSkeletonProfile A.skeleton A.skeletonProfile = A := A.skeleton_profile_reconstruction
example {P : Type u} (p : P) : ¬ Nonempty (ExponentialData (Presentation.operations P) (.var p) (.var p)) := Presentation.no_self_exponential p
example {P : Type u} (Q : Presentation.ProofCongruence P) : Structure Q.fragment.quotientCategory := Q.fragment.quotientStructure
example {P : Type u} (Q : Presentation.ProofCongruence P) : ¬ Nonempty (Q.fragment.QuotientHom .top .bot) := Q.fragment.quotient_preserves_empty (Presentation.empty_hom P)
example {P : Type u} (Q : Presentation.ProofCongruence P) :
    (∀ A B, Subsingleton (Q.fragment.QuotientHom A B)) ↔ Q.Total := Q.fragment.quotient_thin_iff_total
example {P : Type u} {R : Type v} {T : Type w} (σ : P → Formula R) (τ : R → Formula T)
    {A B : Formula P} (f : Presentation.Hom A B) :
    Presentation.transportHom (A.subst_composition σ τ) (B.subst_composition σ τ)
      (Presentation.substitute τ (Presentation.substitute σ f)) = Presentation.substitute (fun p => (σ p).subst τ) f :=
  Presentation.substitute_composition σ τ f
example {P : Type u} {A B : Formula P} (f : Presentation.Hom A B) :
    Presentation.transportHom A.subst_identity B.subst_identity (Presentation.substitute Formula.var f) = f := Presentation.substitute_identity f
example {m : Nat} (n : Fin m → Nat) (x : Fin (FiniteBlocks.total n)) :
    FiniteBlocks.encode n (FiniteBlocks.decode n x) = x := FiniteBlocks.encode_decode n x
example {m : Nat} (n : Fin m → Nat) (x : Fin (FiniteBlocks.total n)) (i : Fin m)
    (lo : FiniteBlocks.prefixSum n i ≤ x.val) (hi : x.val < FiniteBlocks.prefixSum n i+n i) :
    (FiniteBlocks.decode n x).1=i := FiniteBlocks.locator_unique n x i lo hi
example {m k : Nat} (S : ProfileComposition.Data m k) (x : S.Domain) :
    S.delta (FiniteBlocks.encode (fun r => S.n (S.outer r)) x) = FiniteBlocks.encode S.l (S.gamma x) := S.ordinal_square x
example {k : Nat} {l : Fin k → Nat} (M : Formula (Fin k)) (N : ∀ i, Formula (Fin (l i)))
    (x : (M.subst (PatternProfiles.insertion N)).Occ) :
    (PatternProfiles.data M N).gamma (PatternProfiles.chi M N x) = (M.subst (PatternProfiles.insertion N)).label x :=
  PatternProfiles.occurrence_label_square M N x
example {k : Nat} {l : Fin k → Nat} (M : Formula (Fin k)) (N : ∀ i, Formula (Fin (l i)))
    (x : (M.subst (PatternProfiles.insertion N)).Occ) :
    (PatternProfiles.data M N).delta (Fin.cast (PatternProfiles.composite_count M N) ((M.subst (PatternProfiles.insertion N)).occurrenceIndex x)) =
      FiniteBlocks.encode (PatternProfiles.data M N).l ((M.subst (PatternProfiles.insertion N)).label x) :=
  PatternProfiles.actual_ordinal_square M N x
example : (PatternProfiles.Example.delta 1).val+1=3 := PatternProfiles.Example.delta_two
example : [(PatternProfiles.Example.delta 0).val+1,(PatternProfiles.Example.delta 1).val+1,
    (PatternProfiles.Example.delta 2).val+1,(PatternProfiles.Example.delta 3).val+1,
    (PatternProfiles.Example.delta 4).val+1,(PatternProfiles.Example.delta 5).val+1,
    (PatternProfiles.Example.delta 6).val+1,(PatternProfiles.Example.delta 7).val+1] = [4,3,4,1,2,4,3,4] := PatternProfiles.Example.eight_positions
example : (Formula.top : Formula Empty).occurrenceCount=0 := rfl
example : (Formula.neg (.conj (.var 0) (.var 0)) : Formula Nat).occurrenceCount=2 := rfl
example : FiniteBlocks.total (fun i : Fin 3 => if i.val=1 then 0 else 1)=2 := rfl
example : FiniteBlocks.decode (fun i : Fin 3 => if i.val=1 then 0 else 1) (1 : Fin 2) = ⟨2,(0 : Fin 1)⟩ := rfl
example : ProfileComposition.Data 0 0 := ⟨Fin.elim0,Fin.elim0,Fin.elim0,fun i => Fin.elim0 i⟩
example {P : Type u} (p q : P) (A : Formula P) (h : q ≠ p) : Presentation.ManuscriptSubstitution.replace p A q = .var q := Presentation.ManuscriptSubstitution.replace_other p q A h
example {P : Type u} (p : P) (A : Formula P) :
    HEq (Presentation.substitute (Presentation.ManuscriptSubstitution.replace p (.neg A))
      (Presentation.ManuscriptSubstitution.context (.neg (.var p)))) (Presentation.ManuscriptSubstitution.context (.neg (.neg A))) :=
  Presentation.ManuscriptSubstitution.negative_single_context p A
end CompletePaperChecks
'''
anchors=['DosenPetric.FiniteBlocks.'+n for n in ['encode_decode','decode_encode','encode_value','locator_bounds','locator_unique','encode_oneBased','locator_oneBased','total_concat','prefix_concat_left','prefix_concat_right']]+['DosenPetric.Formula.'+n for n in ['occurrenceAt_index','occurrenceIndex_at','profile_index','renameOcc_injective','profile_renaming','substitution_count','substitution_index','skeleton_profile_reconstruction','skeleton_profile_unique','block_square']]+['DosenPetric.ProfileComposition.Data.'+n for n in ['fibre_square','gamma_unique','profile_square','gamma_fibre','ordinal_square','delta_unique','coordinate_oneBased','book_locator','book_formula','a_disjoint','b_disjoint']]+['DosenPetric.PatternProfiles.'+n for n in ['chiInverse_injective','chiInverse_chi','chi_chiInverse','unique_coordinates','occurrence_label_square','renaming_square','composite_count','chiInverse_encoding','actual_ordinal_square','composite_profile','flattened_profile','generalized_composite_skeleton','generalized_composite_reconstruction','Example.eight_positions','Example.delta_two']]+['DosenPetric.Presentation.'+n for n in ['Term.subst_identity_heq','Term.subst_composition_heq','substitute_identity','substitute_composition','substitute_ext','no_self_exponential','contextual_zero_alternative','finiteOccurrenceFunctor','finiteOccurrenceFunctor_faithful','ManuscriptSubstitution.negative_all_contexts','ManuscriptSubstitution.double_negation_square','ManuscriptSubstitution.replace_other','ManuscriptSubstitution.positive_single_context','ManuscriptSubstitution.negative_single_context']]+['DosenPetric.Congruence.'+n for n in ['quotientCategory','quotientStructure','quotientZeroIdentity','quotient_thin_iff_total','quotient_preserves_empty']]+['DosenPetric.ExponentialData.from_toGlobalPoint','DosenPetric.ExponentialData.to_fromGlobalPoint']
p=root/'Checks/Axioms.lean';s=p.read_text()
for a in anchors:
 line='#print axioms '+a+'\n'
 if line not in s:s+=line
 checks+='\n'+line
p.write_text(s);(root/'Checks/CompletePaper.lean').write_text(checks)
print('Integrated 22 modules, exact full-paper public checks and transitive audit anchors')
