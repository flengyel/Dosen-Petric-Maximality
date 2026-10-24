module

public import DosenPetric.GentzenProofReplacement
public import DosenPetric.GentzenSingleMixExamples

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.ReplacementExamples
universe u
variable {P : Type u}

section Binary
variable {Γ Θ Δ Λ : List (NormalForm P)} {A B C : NormalForm P}

theorem mix_left (f h : G P Γ Δ) (g : G P Θ Λ) :
    ((ProofAddress.root : ProofAddress (G.mix f g) (G.mix f g)).down
      (Premise.mix_left f g)).replace h = G.mix h g := rfl

theorem mix_right (f : G P Γ Δ) (g h : G P Θ Λ) :
    ((ProofAddress.root : ProofAddress (G.mix f g) (G.mix f g)).down
      (Premise.mix_right f g)).replace h = G.mix f h := rfl

theorem cut_left (f h : G P Γ (C::Δ)) (g : G P (C::Θ) Λ) :
    ((ProofAddress.root : ProofAddress (G.cut f g) (G.cut f g)).down
      (Premise.cut_left f g)).replace h = G.cut h g := rfl

theorem cut_right (f : G P Γ (C::Δ)) (g h : G P (C::Θ) Λ) :
    ((ProofAddress.root : ProofAddress (G.cut f g) (G.cut f g)).down
      (Premise.cut_right f g)).replace h = G.cut f h := rfl

theorem conjR_left (f h : G P Γ (A::Δ)) (g : G P Θ (B::Λ)) :
    ((ProofAddress.root : ProofAddress (G.conjR f g) (G.conjR f g)).down
      (Premise.conjR_left f g)).replace h = G.conjR h g := rfl

theorem conjR_right (f : G P Γ (A::Δ)) (g h : G P Θ (B::Λ)) :
    ((ProofAddress.root : ProofAddress (G.conjR f g) (G.conjR f g)).down
      (Premise.conjR_right f g)).replace h = G.conjR f h := rfl

theorem disjL_left (f h : G P (A::Γ) Δ) (g : G P (B::Θ) Λ) :
    ((ProofAddress.root : ProofAddress (G.disjL f g) (G.disjL f g)).down
      (Premise.disjL_left f g)).replace h = G.disjL h g := rfl

theorem disjL_right (f : G P (A::Γ) Δ) (g h : G P (B::Θ) Λ) :
    ((ProofAddress.root : ProofAddress (G.disjL f g) (G.disjL f g)).down
      (Premise.disjL_right f g)).replace h = G.disjL f h := rfl
end Binary

/-- Two equal proof values still give two separately replaceable occurrences. -/
theorem identical_siblings (l : Literal P) :
    ((ProofAddress.root : ProofAddress (G.mix (G.identity l) (G.identity l))
      (G.mix (G.identity l) (G.identity l))).down
      (Premise.mix_left (G.identity l) (G.identity l))).replace (G.zero l) =
        G.mix (G.zero l) (G.identity l) ∧
    ((ProofAddress.root : ProofAddress (G.mix (G.identity l) (G.identity l))
      (G.mix (G.identity l) (G.identity l))).down
      (Premise.mix_right (G.identity l) (G.identity l))).replace (G.zero l) =
        G.mix (G.identity l) (G.zero l) ∧
    G.mix (G.zero l) (G.identity l) ≠ G.mix (G.identity l) (G.zero l) := by
  exact ⟨rfl,rfl,fun h => by cases h⟩

def nested (l : Literal P) :=
  G.cut (G.identity l) (G.cut (G.identity l) (G.identity l))
def nestedAddress (l : Literal P) : ProofAddress (nested l) (G.identity l) :=
  (ProofAddress.root.down (Premise.cut_right (G.identity l)
    (G.cut (G.identity l) (G.identity l)))).down
      (Premise.cut_left (G.identity l) (G.identity l))

theorem nested_path (l : Literal P) : (nestedAddress l).path = [1,0] := rfl

theorem nested_one_cut_inserted (l : Literal P) :
    ((nestedAddress l).replace (W5.SinglePremiseMix.Examples.cutIdentity l)).cutCount = 3 ∧
    ((nestedAddress l).replace (W5.SinglePremiseMix.Examples.cutIdentity l)).proofSize = 7 := by
  have hc := (nestedAddress l).replace_cutCount (W5.SinglePremiseMix.Examples.cutIdentity l)
  have hs := (nestedAddress l).replace_proofSize (W5.SinglePremiseMix.Examples.cutIdentity l)
  change _ + 0 = 2 + 1 at hc
  change _ + 1 = 5 + 3 at hs
  omega

theorem signed_nested (p : P) :
    ((nestedAddress (.pos p)).inserted (G.zero (.pos p))).path = [1,0] ∧
    ((nestedAddress (.neg p)).inserted (G.zero (.neg p))).path = [1,0] :=
  ⟨(ProofAddress.inserted_path ..).trans rfl,(ProofAddress.inserted_path ..).trans rfl⟩

def emptyRoot : G Empty [] [.conj .top .top] := G.conjR G.topI G.topI
def emptyLeft : ProofAddress emptyRoot (G.topI : G Empty [] [.top]) :=
  ProofAddress.root.down (Premise.conjR_left G.topI G.topI)

theorem empty_constants :
    emptyLeft.replace G.topI = emptyRoot ∧
    (emptyLeft.inserted G.topI).path = [0] ∧ emptyRoot.CutFree ∧ emptyRoot.Atomized :=
  ⟨emptyLeft.replace_original,(emptyLeft.inserted_path G.topI).trans rfl,rfl,⟨True.intro,True.intro⟩⟩

end DosenPetric.Reduced.Gentzen.ReplacementExamples
