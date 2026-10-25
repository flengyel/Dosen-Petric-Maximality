module

public import DosenPetric.GentzenDisjunctionSuccedentReducer

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace W5.OneDisjunctionAntecedent
variable {A B C : NormalForm P} {F K U L Γ Θ : List (NormalForm P)}

section First
variable (p : ContractionSelection C F K) (f : G P (A::F) Γ) (g : G P (B::U) Θ)
def oldFirst : G P (.disj A B::(K++U)) (Γ++Θ) :=
  (ContractionSelection.fixed (.disj A B) (p.extend U)).performL (Γ++Θ) (G.disjL f g)
def repairFirst : G P (.disj A B::(K++U)) (Γ++Θ) :=
  G.disjL ((p.prependFixed [A]).performL Γ f) g

theorem denoteFirst : ofTerm (repairFirst p f g).denote=ofTerm (oldFirst p f g).denote := by
  have hi : ofTerm ((Route.identity U).head B).product=id (ante (B::U)) :=
    Route.identity_side .conj (B::U)
  have hm : ofTerm (repairFirst p f g).denote=
      ofTerm (Rules.disjLeft (.comp (p.route.head A).product f.denote)
        (.comp ((Route.identity U).head B).product g.denote)) :=
    Rules.disjLeft_congr ((p.prependFixed [A]).performL_denote Γ f)
      (by rw [ofTerm_comp,hi,Laws.id_comp])
  have ho : ofTerm (oldFirst p f g).denote=
      comp (ofTerm ((p.route.parallel (Route.identity U)).head (.disj A B)).product) (ofTerm (G.disjL f g).denote) := by
    rw [oldFirst,ContractionSelection.performL_denote,←p.extend_route U]
    rfl
  exact hm.trans ((Route.head_disjLeft p.route (Route.identity U) f.denote g.denote).symm.trans ho.symm)

theorem old_countFirst : (oldFirst p f g).cutCount=f.cutCount+g.cutCount := by
  rw [oldFirst,ContractionSelection.performL_count]; rfl
theorem repair_countFirst : (repairFirst p f g).cutCount=f.cutCount+g.cutCount := by
  simp only [repairFirst,G.cutCount,ContractionSelection.performL_count]
theorem repair_cutFreeFirst : (repairFirst p f g).CutFree ↔ f.CutFree ∧ g.CutFree := by
  simp only [G.CutFree,repair_countFirst,Nat.add_eq_zero_iff]
theorem repair_atomizedFirst : (repairFirst p f g).Atomized ↔ f.Atomized ∧ g.Atomized := by
  simp only [repairFirst,G.Atomized,ContractionSelection.performL_atomized]
end First
section Second
variable (q : ContractionSelection C U L) (f : G P (A::F) Γ) (g : G P (B::U) Θ)
def oldSecond : G P (.disj A B::(F++L)) (Γ++Θ) :=
  (ContractionSelection.fixed (.disj A B) (q.prependFixed F)).performL (Γ++Θ) (G.disjL f g)
def repairSecond : G P (.disj A B::(F++L)) (Γ++Θ) :=
  G.disjL f ((q.prependFixed [B]).performL Θ g)

theorem denoteSecond : ofTerm (repairSecond q f g).denote=ofTerm (oldSecond q f g).denote := by
  have hi : ofTerm ((Route.identity F).head A).product=id (ante (A::F)) :=
    Route.identity_side .conj (A::F)
  have hm : ofTerm (repairSecond q f g).denote=
      ofTerm (Rules.disjLeft (.comp ((Route.identity F).head A).product f.denote)
        (.comp (q.route.head B).product g.denote)) :=
    Rules.disjLeft_congr (by rw [ofTerm_comp,hi,Laws.id_comp])
      ((q.prependFixed [B]).performL_denote Θ g)
  have ho : ofTerm (oldSecond q f g).denote=
      comp (ofTerm (((Route.identity F).parallel q.route).head (.disj A B)).product) (ofTerm (G.disjL f g).denote) := by
    rw [oldSecond,ContractionSelection.performL_denote,←q.prepend_route F]
    rfl
  exact hm.trans ((Route.head_disjLeft (Route.identity F) q.route f.denote g.denote).symm.trans ho.symm)

theorem old_countSecond : (oldSecond q f g).cutCount=f.cutCount+g.cutCount := by
  rw [oldSecond,ContractionSelection.performL_count]; rfl
theorem repair_countSecond : (repairSecond q f g).cutCount=f.cutCount+g.cutCount := by
  simp only [repairSecond,G.cutCount,ContractionSelection.performL_count]
theorem repair_cutFreeSecond : (repairSecond q f g).CutFree ↔ f.CutFree ∧ g.CutFree := by
  simp only [G.CutFree,repair_countSecond,Nat.add_eq_zero_iff]
theorem repair_atomizedSecond : (repairSecond q f g).Atomized ↔ f.Atomized ∧ g.Atomized := by
  simp only [repairSecond,G.Atomized,ContractionSelection.performL_atomized]
end Second
end W5.OneDisjunctionAntecedent
end DosenPetric.Reduced.Gentzen
