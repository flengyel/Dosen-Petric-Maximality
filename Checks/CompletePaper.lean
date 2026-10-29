module
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

#print axioms DosenPetric.FiniteBlocks.encode_decode

#print axioms DosenPetric.FiniteBlocks.decode_encode

#print axioms DosenPetric.FiniteBlocks.encode_value

#print axioms DosenPetric.FiniteBlocks.locator_bounds

#print axioms DosenPetric.FiniteBlocks.locator_unique

#print axioms DosenPetric.FiniteBlocks.encode_oneBased

#print axioms DosenPetric.FiniteBlocks.locator_oneBased

#print axioms DosenPetric.FiniteBlocks.total_concat

#print axioms DosenPetric.FiniteBlocks.prefix_concat_left

#print axioms DosenPetric.FiniteBlocks.prefix_concat_right

#print axioms DosenPetric.Formula.occurrenceAt_index

#print axioms DosenPetric.Formula.occurrenceIndex_at

#print axioms DosenPetric.Formula.profile_index

#print axioms DosenPetric.Formula.renameOcc_injective

#print axioms DosenPetric.Formula.profile_renaming

#print axioms DosenPetric.Formula.substitution_count

#print axioms DosenPetric.Formula.substitution_index

#print axioms DosenPetric.Formula.skeleton_profile_reconstruction

#print axioms DosenPetric.Formula.skeleton_profile_unique

#print axioms DosenPetric.Formula.block_square

#print axioms DosenPetric.ProfileComposition.Data.fibre_square

#print axioms DosenPetric.ProfileComposition.Data.gamma_unique

#print axioms DosenPetric.ProfileComposition.Data.profile_square

#print axioms DosenPetric.ProfileComposition.Data.gamma_fibre

#print axioms DosenPetric.ProfileComposition.Data.ordinal_square

#print axioms DosenPetric.ProfileComposition.Data.delta_unique

#print axioms DosenPetric.ProfileComposition.Data.coordinate_oneBased

#print axioms DosenPetric.ProfileComposition.Data.book_locator

#print axioms DosenPetric.ProfileComposition.Data.book_formula

#print axioms DosenPetric.ProfileComposition.Data.a_disjoint

#print axioms DosenPetric.ProfileComposition.Data.b_disjoint

#print axioms DosenPetric.PatternProfiles.chiInverse_injective

#print axioms DosenPetric.PatternProfiles.chiInverse_chi

#print axioms DosenPetric.PatternProfiles.chi_chiInverse

#print axioms DosenPetric.PatternProfiles.unique_coordinates

#print axioms DosenPetric.PatternProfiles.occurrence_label_square

#print axioms DosenPetric.PatternProfiles.renaming_square

#print axioms DosenPetric.PatternProfiles.composite_count

#print axioms DosenPetric.PatternProfiles.chiInverse_encoding

#print axioms DosenPetric.PatternProfiles.actual_ordinal_square

#print axioms DosenPetric.PatternProfiles.composite_profile

#print axioms DosenPetric.PatternProfiles.flattened_profile

#print axioms DosenPetric.PatternProfiles.generalized_composite_skeleton

#print axioms DosenPetric.PatternProfiles.generalized_composite_reconstruction

#print axioms DosenPetric.PatternProfiles.Example.eight_positions

#print axioms DosenPetric.PatternProfiles.Example.delta_two

#print axioms DosenPetric.Presentation.Term.subst_identity_heq

#print axioms DosenPetric.Presentation.Term.subst_composition_heq

#print axioms DosenPetric.Presentation.substitute_identity

#print axioms DosenPetric.Presentation.substitute_composition

#print axioms DosenPetric.Presentation.substitute_ext

#print axioms DosenPetric.Presentation.no_self_exponential

#print axioms DosenPetric.Presentation.contextual_zero_alternative

#print axioms DosenPetric.Presentation.finiteOccurrenceFunctor

#print axioms DosenPetric.Presentation.finiteOccurrenceFunctor_faithful

#print axioms DosenPetric.Presentation.ManuscriptSubstitution.negative_all_contexts

#print axioms DosenPetric.Presentation.ManuscriptSubstitution.double_negation_square

#print axioms DosenPetric.Presentation.ManuscriptSubstitution.replace_other

#print axioms DosenPetric.Presentation.ManuscriptSubstitution.positive_single_context

#print axioms DosenPetric.Presentation.ManuscriptSubstitution.negative_single_context

#print axioms DosenPetric.Congruence.quotientCategory

#print axioms DosenPetric.Congruence.quotientStructure

#print axioms DosenPetric.Congruence.quotientZeroIdentity

#print axioms DosenPetric.Congruence.quotient_thin_iff_total

#print axioms DosenPetric.Congruence.quotient_preserves_empty

#print axioms DosenPetric.ExponentialData.from_toGlobalPoint

#print axioms DosenPetric.ExponentialData.to_fromGlobalPoint
