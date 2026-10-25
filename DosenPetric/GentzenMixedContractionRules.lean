module

public import DosenPetric.GentzenMixedSelectionComponents

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.W5.MixedPremiseMix
universe u
variable {P : Type u} {C : NormalForm P} {F K U L : List (NormalForm P)}
variable (p : ContractionSelection C F K) (q : ContractionSelection C U L)

theorem total_bound : 2 ≤ (p.chain q).gs.length := by
  rw [ContractionSelection.count,ContractionSelection.chain_count]
  have hp:=p.arity_pos
  have hq:=q.arity_pos
  omega

section Left
variable {Δ Λ : List (NormalForm P)} (f : G P U Δ) (g : G P F Λ)
def oldL : G P (p.erased++L) (Λ++Δ) :=
  (p.chain q).block.applyL (total_bound p q) _ (G.mix f g)
def middleL : G P (K++L) (Λ++Δ) := G.mix (q.performL Δ f) (p.performL Λ g)
def newL : G P (p.erased++L) (Λ++Δ) :=
  (p.mergeBlock q).applyL (Nat.le_refl 2) _ (middleL p q f g)

theorem denoteL : ofTerm (newL p q f g).denote = ofTerm (oldL p q f g).denote := by
  have hm : ofTerm (middleL p q f g).denote =
      ofTerm (Rules.mix (.comp q.route.product f.denote) (.comp p.route.product g.denote)) :=
    Rules.mix_congr (q.performL_denote Δ f) (p.performL_denote Λ g)
  have hp := (p.chain q).block.denoteL (total_bound p q) _ (G.mix f g)
  rw [←ContractionSelection.route_eq] at hp
  have hs := p.chain_square q .conj
  change ofTerm (p.chain q).route.product =
    comp (ofTerm (p.mergeBlock q).route.product) (ofTerm (p.route.parallel q.route).product) at hs
  calc
    ofTerm (newL p q f g).denote = comp (ofTerm (p.mergeBlock q).route.product)
        (ofTerm (middleL p q f g).denote) := (p.mergeBlock q).denoteL ..
    _ = comp (ofTerm (p.mergeBlock q).route.product)
        (comp (ofTerm (p.route.parallel q.route).product) (ofTerm (G.mix f g).denote)) := by
      rw [hm,←p.parallel_mixL q f.denote g.denote]
      rfl
    _ = ofTerm (oldL p q f g).denote := by rw [←Laws.assoc,←hs,←hp]; rfl

theorem old_countL : (oldL p q f g).cutCount = f.cutCount+g.cutCount := by
  simp only [oldL,ContractionBlock.countL,G.cutCount]
theorem new_countL : (newL p q f g).cutCount = f.cutCount+g.cutCount := by
  simp only [newL,middleL,ContractionBlock.countL,G.cutCount,ContractionSelection.performL_count]
theorem new_atomizedL : (newL p q f g).Atomized ↔ f.Atomized ∧ g.Atomized := by
  simp only [newL,middleL,ContractionBlock.atomizedL,G.Atomized,ContractionSelection.performL_atomized]
theorem old_atomizedL : (oldL p q f g).Atomized ↔ f.Atomized ∧ g.Atomized := by
  simp only [oldL,ContractionBlock.atomizedL,G.Atomized]
theorem new_cutFreeL : (newL p q f g).CutFree ↔ f.CutFree ∧ g.CutFree := by
  simp only [G.CutFree,new_countL,Nat.add_eq_zero_iff]
theorem old_cutFreeL : (oldL p q f g).CutFree ↔ f.CutFree ∧ g.CutFree := by
  simp only [G.CutFree,old_countL,Nat.add_eq_zero_iff]
theorem relationL : (newL p q f g).relation = (oldL p q f g).relation :=
  congrArg occurrenceMap (denoteL p q f g)
end Left

section Right
variable {Δ Λ : List (NormalForm P)} (f : G P Δ U) (g : G P Λ F)
def oldR : G P (Λ++Δ) (p.erased++L) :=
  (p.chain q).block.applyR (total_bound p q) _ (G.mix f g)
def middleR : G P (Λ++Δ) (K++L) := G.mix (q.performR Δ f) (p.performR Λ g)
def newR : G P (Λ++Δ) (p.erased++L) :=
  (p.mergeBlock q).applyR (Nat.le_refl 2) _ (middleR p q f g)

theorem denoteR : ofTerm (newR p q f g).denote = ofTerm (oldR p q f g).denote := by
  have hm : ofTerm (middleR p q f g).denote =
      ofTerm (Rules.mix (.comp f.denote q.route.coproduct) (.comp g.denote p.route.coproduct)) :=
    Rules.mix_congr (q.performR_denote Δ f) (p.performR_denote Λ g)
  have hp := (p.chain q).block.denoteR (total_bound p q) _ (G.mix f g)
  rw [←ContractionSelection.route_eq] at hp
  have hs := p.chain_square q .disj
  change ofTerm (p.chain q).route.coproduct =
    comp (ofTerm (p.route.parallel q.route).coproduct) (ofTerm (p.mergeBlock q).route.coproduct) at hs
  calc
    ofTerm (newR p q f g).denote = comp (ofTerm (middleR p q f g).denote)
        (ofTerm (p.mergeBlock q).route.coproduct) := (p.mergeBlock q).denoteR ..
    _ = comp (comp (ofTerm (G.mix f g).denote) (ofTerm (p.route.parallel q.route).coproduct))
        (ofTerm (p.mergeBlock q).route.coproduct) := by
      rw [hm,←p.parallel_mixR q f.denote g.denote]
      rfl
    _ = ofTerm (oldR p q f g).denote := by rw [Laws.assoc,←hs,←hp]; rfl

theorem old_countR : (oldR p q f g).cutCount = f.cutCount+g.cutCount := by
  simp only [oldR,ContractionBlock.countR,G.cutCount]
theorem new_countR : (newR p q f g).cutCount = f.cutCount+g.cutCount := by
  simp only [newR,middleR,ContractionBlock.countR,G.cutCount,ContractionSelection.performR_count]
theorem new_atomizedR : (newR p q f g).Atomized ↔ f.Atomized ∧ g.Atomized := by
  simp only [newR,middleR,ContractionBlock.atomizedR,G.Atomized,ContractionSelection.performR_atomized]
theorem old_atomizedR : (oldR p q f g).Atomized ↔ f.Atomized ∧ g.Atomized := by
  simp only [oldR,ContractionBlock.atomizedR,G.Atomized]
theorem new_cutFreeR : (newR p q f g).CutFree ↔ f.CutFree ∧ g.CutFree := by
  simp only [G.CutFree,new_countR,Nat.add_eq_zero_iff]
theorem old_cutFreeR : (oldR p q f g).CutFree ↔ f.CutFree ∧ g.CutFree := by
  simp only [G.CutFree,old_countR,Nat.add_eq_zero_iff]
theorem relationR : (newR p q f g).relation = (oldR p q f g).relation :=
  congrArg occurrenceMap (denoteR p q f g)
end Right

end DosenPetric.Reduced.Gentzen.W5.MixedPremiseMix
