module

public import DosenPetric.GentzenProofReplacement
public import DosenPetric.GentzenOtherMixRules
public import DosenPetric.GentzenSingleMixExamples

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.W5.OtherPremiseMix
universe u
variable {P : Type u} {F K Φ Ψ Δ Γ₀ Δ₀ : List (NormalForm P)}
variable (d : ContractionBlock P F K) (hn : 2 ≤ d.gs.length)
variable (f : G P Φ Ψ)

section L
variable (g : G P F Δ) {root : G P Γ₀ Δ₀}
variable (a : ProofAddress root (oldL d hn f g))

theorem replace_denoteL :
    ofTerm (a.replace (newL d hn f g)).denote = ofTerm root.denote :=
  a.replace_denote _ (denoteL d hn f g)
theorem replace_relationL : (a.replace (newL d hn f g)).relation = root.relation :=
  a.replace_relation _ (denoteL d hn f g)
theorem replace_countL : (a.replace (newL d hn f g)).cutCount = root.cutCount :=
  a.replace_count_eq _ ((new_countL d hn f g).trans (old_countL d hn f g).symm)
theorem replace_cutFreeL (hr : root.CutFree) : (a.replace (newL d hn f g)).CutFree :=
  a.replace_cutFree _ hr ((new_cutFreeL d hn f g).mpr ((old_cutFreeL d hn f g).mp (a.cutFree hr)))
theorem replace_atomizedL (hr : root.Atomized) : (a.replace (newL d hn f g)).Atomized :=
  a.replace_atomized _ hr ((new_atomizedL d hn f g).mpr ((old_atomizedL d hn f g).mp (a.atomized hr)))
end L

section R
variable (g : G P Δ F) {root : G P Γ₀ Δ₀}
variable (a : ProofAddress root (oldR d hn f g))

theorem replace_denoteR :
    ofTerm (a.replace (newR d hn f g)).denote = ofTerm root.denote :=
  a.replace_denote _ (denoteR d hn f g)
theorem replace_relationR : (a.replace (newR d hn f g)).relation = root.relation :=
  a.replace_relation _ (denoteR d hn f g)
theorem replace_countR : (a.replace (newR d hn f g)).cutCount = root.cutCount :=
  a.replace_count_eq _ ((new_countR d hn f g).trans (old_countR d hn f g).symm)
theorem replace_cutFreeR (hr : root.CutFree) : (a.replace (newR d hn f g)).CutFree :=
  a.replace_cutFree _ hr ((new_cutFreeR d hn f g).mpr ((old_cutFreeR d hn f g).mp (a.cutFree hr)))
theorem replace_atomizedR (hr : root.Atomized) : (a.replace (newR d hn f g)).Atomized :=
  a.replace_atomized _ hr ((new_atomizedR d hn f g).mpr ((old_atomizedR d hn f g).mp (a.atomized hr)))
end R
end DosenPetric.Reduced.Gentzen.W5.OtherPremiseMix

namespace DosenPetric.Reduced.Gentzen.RewriteIntegration
universe u
variable {P : Type u} {Γ Δ Θ Λ : List (NormalForm P)}

/-- A concrete two-level surrounding proof with an unchanged mix sibling. -/
def surround (A : NormalForm P) (s : G P Θ Λ) (q : G P Γ Δ) :
    G P (Θ++A::Γ) (Λ++Δ) := G.mix (G.thinL [] Γ Δ A q) s

def address (A : NormalForm P) (s : G P Θ Λ) (q : G P Γ Δ) :
    ProofAddress (surround A s q) q :=
  (ProofAddress.root.down (Premise.mix_left (G.thinL [] Γ Δ A q) s)).down
    (Premise.thinL [] Γ Δ A q)

theorem address_path (A : NormalForm P) (s : G P Θ Λ) (q : G P Γ Δ) :
    (address A s q).path = [0,0] := rfl

theorem replace_surround (A : NormalForm P) (s : G P Θ Λ) (q h : G P Γ Δ) :
    (address A s q).replace h = surround A s h := rfl

open W5.OtherPremiseMix W5.SinglePremiseMix.Examples

theorem actual_w5 (l : Literal P) :
    ofTerm (surround (.lit l) (cutIdentity l)
      (newL (tagged (.lit l)) (Nat.le_refl 2) (cutIdentity l) (gLeft l))).denote =
    ofTerm (surround (.lit l) (cutIdentity l)
      (oldL (tagged (.lit l)) (Nat.le_refl 2) (cutIdentity l) (gLeft l))).denote :=
  (address (.lit l) (cutIdentity l)
    (oldL (tagged (.lit l)) (Nat.le_refl 2) (cutIdentity l) (gLeft l))).replace_denote
      (newL (tagged (.lit l)) (Nat.le_refl 2) (cutIdentity l) (gLeft l))
      (denoteL (tagged (.lit l)) (Nat.le_refl 2) (cutIdentity l) (gLeft l))

theorem actual_w5_count (l : Literal P) :
    (surround (.lit l) (cutIdentity l)
      (newL (tagged (.lit l)) (Nat.le_refl 2) (cutIdentity l) (gLeft l))).cutCount = 3 := by
  have h := replace_countL (tagged (.lit l)) (Nat.le_refl 2) (cutIdentity l) (gLeft l)
    (address (.lit l) (cutIdentity l) _)
  have ho : (surround (.lit l) (cutIdentity l)
      (oldL (tagged (.lit l)) (Nat.le_refl 2) (cutIdentity l) (gLeft l))).cutCount = 3 := by
    change (oldL (tagged (.lit l)) (Nat.le_refl 2) (cutIdentity l) (gLeft l)).cutCount + 1 = 3
    rw [old_countL]
    rfl
  exact h.trans ho

theorem actual_w5_atomized (l : Literal P) :
    (surround (.lit l) (G.identity l)
      (newL (two (.lit l)) (Nat.le_refl 2) (G.identity l)
        (G.thinL [] [.lit l] [.lit l] (.lit l) (G.identity l)))).Atomized := by
  apply replace_atomizedL (two (.lit l)) (Nat.le_refl 2) (G.identity l)
    (G.thinL [] [.lit l] [.lit l] (.lit l) (G.identity l))
    (address (.lit l) (G.identity l) _)
  change (AtomicFormula (.lit l) ∧ _) ∧ _
  exact ⟨⟨True.intro,(old_atomizedL ..).mpr ⟨True.intro,⟨True.intro,True.intro⟩⟩⟩,True.intro⟩

theorem actual_w5_cutFree (l : Literal P) :
    (surround (.lit l) (G.identity l)
      (newL (two (.lit l)) (Nat.le_refl 2) (G.identity l)
        (G.thinL [] [.lit l] [.lit l] (.lit l) (G.identity l)))).CutFree := by
  apply replace_cutFreeL (two (.lit l)) (Nat.le_refl 2) (G.identity l)
    (G.thinL [] [.lit l] [.lit l] (.lit l) (G.identity l))
    (address (.lit l) (G.identity l) _)
  simp only [surround,G.CutFree,G.cutCount,old_countL]

theorem empty_w5_right :
    ofTerm (surround (.top : NormalForm Empty) G.topI
      (newR (two .bot) (Nat.le_refl 2) G.botE (constRight .bot 2))).denote =
    ofTerm (surround (.top : NormalForm Empty) G.topI
      (oldR (two .bot) (Nat.le_refl 2) G.botE (constRight .bot 2))).denote :=
  (address (.top : NormalForm Empty) G.topI
    (oldR (two .bot) (Nat.le_refl 2) G.botE (constRight .bot 2))).replace_denote
      (newR (two .bot) (Nat.le_refl 2) G.botE (constRight .bot 2))
      (denoteR (two .bot) (Nat.le_refl 2) G.botE (constRight .bot 2))

end DosenPetric.Reduced.Gentzen.RewriteIntegration
