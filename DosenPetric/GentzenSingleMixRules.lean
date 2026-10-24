module

public import DosenPetric.GentzenContractionMixComponents
public import DosenPetric.GentzenSingleMixFibers
public import DosenPetric.GentzenAnalysisMacros

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.W5.SinglePremiseMix
universe u
variable {P : Type u} {F K : List (NormalForm P)}
variable (d : ContractionBlock P F K) (hn : 2 ≤ d.gs.length)

section L
variable {Φ Ψ Δ : List (NormalForm P)} (f : G P Φ Ψ) (g : G P F Δ)
def innerL : G P K Δ := d.applyL hn Δ g
def oldL : G P (K++Φ) (Δ++Ψ) := (d.extend Φ).applyL hn _ (G.mix f g)
def newL : G P (K++Φ) (Δ++Ψ) := G.mix f (innerL d hn g)
theorem denoteL : ofTerm (newL d hn f g).denote = ofTerm (oldL d hn f g).denote := by
  have hi : ofTerm (innerL d hn g).denote = ofTerm (.comp d.route.product g.denote) := d.denoteL hn Δ g
  have he : ofTerm (Rules.mix f.denote (innerL d hn g).denote) =
      ofTerm (Rules.mix f.denote (.comp d.route.product g.denote)) := Rules.mix_congr rfl hi
  have ho := ((d.extend Φ).denoteL hn _ (G.mix f g)).trans (d.mixL f.denote g.denote)
  exact he.trans ho.symm
theorem old_countL : (oldL d hn f g).cutCount = f.cutCount+g.cutCount := by
  simp only [oldL,ContractionBlock.countL,G.cutCount]
theorem new_countL : (newL d hn f g).cutCount = f.cutCount+g.cutCount := by
  simp only [newL,innerL,G.cutCount,ContractionBlock.countL]
theorem old_cutFreeL : (oldL d hn f g).CutFree ↔ f.CutFree ∧ g.CutFree := by
  simp only [G.CutFree,old_countL,Nat.add_eq_zero_iff]
theorem new_cutFreeL : (newL d hn f g).CutFree ↔ f.CutFree ∧ g.CutFree := by
  simp only [G.CutFree,new_countL,Nat.add_eq_zero_iff]
theorem old_atomizedL : (oldL d hn f g).Atomized ↔ f.Atomized ∧ g.Atomized := by
  simp only [oldL,ContractionBlock.atomizedL,G.Atomized]
theorem new_atomizedL : (newL d hn f g).Atomized ↔ f.Atomized ∧ g.Atomized := by
  simp only [newL,innerL,G.Atomized,ContractionBlock.atomizedL]
theorem relationL : (newL d hn f g).relation = (oldL d hn f g).relation :=
  congrArg occurrenceMap (denoteL d hn f g)
end L

section R
variable {Φ Ψ Δ : List (NormalForm P)} (f : G P Φ Ψ) (g : G P Δ F)
def innerR : G P Δ K := d.applyR hn Δ g
def oldR : G P (Δ++Φ) (K++Ψ) := (d.extend Ψ).applyR hn _ (G.mix f g)
def newR : G P (Δ++Φ) (K++Ψ) := G.mix f (innerR d hn g)
theorem denoteR : ofTerm (newR d hn f g).denote = ofTerm (oldR d hn f g).denote := by
  have hi : ofTerm (innerR d hn g).denote = ofTerm (.comp g.denote d.route.coproduct) := d.denoteR hn Δ g
  have he : ofTerm (Rules.mix f.denote (innerR d hn g).denote) =
      ofTerm (Rules.mix f.denote (.comp g.denote d.route.coproduct)) := Rules.mix_congr rfl hi
  have ho := ((d.extend Ψ).denoteR hn _ (G.mix f g)).trans (d.mixR f.denote g.denote)
  exact he.trans ho.symm
theorem old_countR : (oldR d hn f g).cutCount = f.cutCount+g.cutCount := by
  simp only [oldR,ContractionBlock.countR,G.cutCount]
theorem new_countR : (newR d hn f g).cutCount = f.cutCount+g.cutCount := by
  simp only [newR,innerR,G.cutCount,ContractionBlock.countR]
theorem old_cutFreeR : (oldR d hn f g).CutFree ↔ f.CutFree ∧ g.CutFree := by
  simp only [G.CutFree,old_countR,Nat.add_eq_zero_iff]
theorem new_cutFreeR : (newR d hn f g).CutFree ↔ f.CutFree ∧ g.CutFree := by
  simp only [G.CutFree,new_countR,Nat.add_eq_zero_iff]
theorem old_atomizedR : (oldR d hn f g).Atomized ↔ f.Atomized ∧ g.Atomized := by
  simp only [oldR,ContractionBlock.atomizedR,G.Atomized]
theorem new_atomizedR : (newR d hn f g).Atomized ↔ f.Atomized ∧ g.Atomized := by
  simp only [newR,innerR,G.Atomized,ContractionBlock.atomizedR]
theorem relationR : (newR d hn f g).relation = (oldR d hn f g).relation :=
  congrArg occurrenceMap (denoteR d hn f g)
end R

abbrev block (C : NormalForm P) (gs : List (List (NormalForm P))) (Θ : List (NormalForm P)) :
    ContractionBlock P (repeated C gs++Θ) (gaps gs++C::Θ) := ⟨C,gs,Θ,rfl,rfl⟩
theorem single_premise_left (C : NormalForm P) (gs : List (List (NormalForm P)))
    (Θ Φ Ψ Δ : List (NormalForm P)) (hn : 2 ≤ gs.length)
    (f : G P Φ Ψ) (g : G P (repeated C gs++Θ) Δ) :
    ofTerm (newL (block C gs Θ) hn f g).denote = ofTerm (oldL (block C gs Θ) hn f g).denote := denoteL ..
theorem single_premise_right (C : NormalForm P) (gs : List (List (NormalForm P)))
    (Θ Φ Ψ Δ : List (NormalForm P)) (hn : 2 ≤ gs.length)
    (f : G P Φ Ψ) (g : G P Δ (repeated C gs++Θ)) :
    ofTerm (newR (block C gs Θ) hn f g).denote = ofTerm (oldR (block C gs Θ) hn f g).denote := denoteR ..
end DosenPetric.Reduced.Gentzen.W5.SinglePremiseMix
