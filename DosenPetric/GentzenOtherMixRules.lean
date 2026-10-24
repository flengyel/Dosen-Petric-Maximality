module

public import DosenPetric.GentzenPrependMixComponents
public import DosenPetric.GentzenSingleMixRules
public import DosenPetric.GentzenOtherMixFibers
public import DosenPetric.GentzenAnalysisMacros

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.W5.OtherPremiseMix
universe u
variable {P : Type u} {F K : List (NormalForm P)}
variable (d : ContractionBlock P F K) (hn : 2 ≤ d.gs.length)

section L
variable {Φ Ψ Δ : List (NormalForm P)} (f : G P Φ Ψ) (g : G P F Δ)
def innerL : G P K Δ := d.applyL hn Δ g
def oldL : G P (Φ++K) (Ψ++Δ) := (d.prepend hn Φ).applyL (d.prepend_bound hn Φ) _ (G.mix g f)
def newL : G P (Φ++K) (Ψ++Δ) := G.mix (innerL d hn g) f
theorem denoteL : ofTerm (newL d hn f g).denote = ofTerm (oldL d hn f g).denote := by
  have hi : ofTerm (innerL d hn g).denote = ofTerm (.comp d.route.product g.denote) := d.denoteL hn Δ g
  have he : ofTerm (Rules.mix (innerL d hn g).denote f.denote) =
      ofTerm (Rules.mix (.comp d.route.product g.denote) f.denote) := Rules.mix_congr hi rfl
  have ho := ((d.prepend hn Φ).denoteL (d.prepend_bound hn Φ) _ (G.mix g f)).trans (d.otherMixL hn g.denote f.denote)
  exact he.trans ho.symm
theorem old_countL : (oldL d hn f g).cutCount = f.cutCount+g.cutCount := by
  simp only [oldL,ContractionBlock.countL,G.cutCount]
  exact Nat.add_comm ..
theorem new_countL : (newL d hn f g).cutCount = f.cutCount+g.cutCount := by
  simp only [newL,innerL,G.cutCount,ContractionBlock.countL]
  exact Nat.add_comm ..
theorem old_cutFreeL : (oldL d hn f g).CutFree ↔ f.CutFree ∧ g.CutFree := by
  simp only [G.CutFree,old_countL,Nat.add_eq_zero_iff]
theorem new_cutFreeL : (newL d hn f g).CutFree ↔ f.CutFree ∧ g.CutFree := by
  simp only [G.CutFree,new_countL,Nat.add_eq_zero_iff]
theorem old_atomizedL : (oldL d hn f g).Atomized ↔ f.Atomized ∧ g.Atomized := by
  simp only [oldL,ContractionBlock.atomizedL,G.Atomized]
  exact and_comm
theorem new_atomizedL : (newL d hn f g).Atomized ↔ f.Atomized ∧ g.Atomized := by
  simp only [newL,innerL,G.Atomized,ContractionBlock.atomizedL]
  exact and_comm
theorem relationL : (newL d hn f g).relation = (oldL d hn f g).relation :=
  congrArg occurrenceMap (denoteL d hn f g)
end L

section R
variable {Φ Ψ Δ : List (NormalForm P)} (f : G P Φ Ψ) (g : G P Δ F)
def innerR : G P Δ K := d.applyR hn Δ g
def oldR : G P (Φ++Δ) (Ψ++K) := (d.prepend hn Ψ).applyR (d.prepend_bound hn Ψ) _ (G.mix g f)
def newR : G P (Φ++Δ) (Ψ++K) := G.mix (innerR d hn g) f
theorem denoteR : ofTerm (newR d hn f g).denote = ofTerm (oldR d hn f g).denote := by
  have hi : ofTerm (innerR d hn g).denote = ofTerm (.comp g.denote d.route.coproduct) := d.denoteR hn Δ g
  have he : ofTerm (Rules.mix (innerR d hn g).denote f.denote) =
      ofTerm (Rules.mix (.comp g.denote d.route.coproduct) f.denote) := Rules.mix_congr hi rfl
  have ho := ((d.prepend hn Ψ).denoteR (d.prepend_bound hn Ψ) _ (G.mix g f)).trans (d.otherMixR hn g.denote f.denote)
  exact he.trans ho.symm
theorem old_countR : (oldR d hn f g).cutCount = f.cutCount+g.cutCount := by
  simp only [oldR,ContractionBlock.countR,G.cutCount]
  exact Nat.add_comm ..
theorem new_countR : (newR d hn f g).cutCount = f.cutCount+g.cutCount := by
  simp only [newR,innerR,G.cutCount,ContractionBlock.countR]
  exact Nat.add_comm ..
theorem old_cutFreeR : (oldR d hn f g).CutFree ↔ f.CutFree ∧ g.CutFree := by
  simp only [G.CutFree,old_countR,Nat.add_eq_zero_iff]
theorem new_cutFreeR : (newR d hn f g).CutFree ↔ f.CutFree ∧ g.CutFree := by
  simp only [G.CutFree,new_countR,Nat.add_eq_zero_iff]
theorem old_atomizedR : (oldR d hn f g).Atomized ↔ f.Atomized ∧ g.Atomized := by
  simp only [oldR,ContractionBlock.atomizedR,G.Atomized]
  exact and_comm
theorem new_atomizedR : (newR d hn f g).Atomized ↔ f.Atomized ∧ g.Atomized := by
  simp only [newR,innerR,G.Atomized,ContractionBlock.atomizedR]
  exact and_comm
theorem relationR : (newR d hn f g).relation = (oldR d hn f g).relation :=
  congrArg occurrenceMap (denoteR d hn f g)
end R

theorem other_premise_left (C : NormalForm P) (gs : List (List (NormalForm P)))
    (Θ Φ Ψ Δ : List (NormalForm P)) (hn : 2 ≤ gs.length)
    (f : G P Φ Ψ) (g : G P (repeated C gs++Θ) Δ) :
    ofTerm (newL (SinglePremiseMix.block C gs Θ) hn f g).denote = ofTerm (oldL (SinglePremiseMix.block C gs Θ) hn f g).denote := denoteL ..
theorem other_premise_right (C : NormalForm P) (gs : List (List (NormalForm P)))
    (Θ Φ Ψ Δ : List (NormalForm P)) (hn : 2 ≤ gs.length)
    (f : G P Φ Ψ) (g : G P Δ (repeated C gs++Θ)) :
    ofTerm (newR (SinglePremiseMix.block C gs Θ) hn f g).denote = ofTerm (oldR (SinglePremiseMix.block C gs Θ) hn f g).denote := denoteR ..
end DosenPetric.Reduced.Gentzen.W5.OtherPremiseMix
