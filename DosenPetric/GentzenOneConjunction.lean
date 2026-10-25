module

public import DosenPetric.GentzenParametricConjunctionRanks

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace ContractionSelection

theorem prepend_route {C : NormalForm P} {F K : List (NormalForm P)}
    (p : ContractionSelection C F K) (Ξ : List (NormalForm P)) :
    (p.prependFixed Ξ).route=(Route.identity Ξ).parallel p.route := by
  apply Route.ext_get
  intro A a
  cases At.cases_append Ξ F a with
  | inl h => obtain ⟨a,rfl⟩:=h; rw [p.prepend_before,Route.parallel_before,Route.get_identity]
  | inr h => obtain ⟨a,rfl⟩:=h; rw [p.prepend_shift,Route.parallel_shift]
end ContractionSelection
namespace W5.OneConjunction
variable {A B C : NormalForm P} {F K U L Γ Θ : List (NormalForm P)}

section First
variable (p : ContractionSelection C F K) (f : G P Γ (A::F)) (g : G P Θ (B::U))
def oldFirst : G P (Γ++Θ) (.conj A B::(K++U)) :=
  (ContractionSelection.fixed (.conj A B) (p.extend U)).performR (Γ++Θ) (G.conjR f g)
def repairFirst : G P (Γ++Θ) (.conj A B::(K++U)) :=
  G.conjR ((p.prependFixed [A]).performR Γ f) g

theorem denoteFirst : ofTerm (repairFirst p f g).denote=ofTerm (oldFirst p f g).denote := by
  have hi : ofTerm ((Route.identity U).head B).coproduct=id (succ (B::U)) :=
    Route.identity_side .disj (B::U)
  have hm : ofTerm (repairFirst p f g).denote=
      ofTerm (Rules.conjRight (.comp f.denote (p.route.head A).coproduct)
        (.comp g.denote ((Route.identity U).head B).coproduct)) :=
    Rules.conjRight_congr ((p.prependFixed [A]).performR_denote Γ f)
      (by rw [ofTerm_comp,hi,Laws.comp_id])
  have ho : ofTerm (oldFirst p f g).denote=
      comp (ofTerm (G.conjR f g).denote) (ofTerm ((p.route.parallel (Route.identity U)).head (.conj A B)).coproduct) := by
    rw [oldFirst,ContractionSelection.performR_denote,←p.extend_route U]
    rfl
  exact hm.trans ((Route.head_conjRight p.route (Route.identity U) f.denote g.denote).symm.trans ho.symm)

theorem old_countFirst : (oldFirst p f g).cutCount=f.cutCount+g.cutCount := by
  rw [oldFirst,ContractionSelection.performR_count]; rfl
theorem repair_countFirst : (repairFirst p f g).cutCount=f.cutCount+g.cutCount := by
  simp only [repairFirst,G.cutCount,ContractionSelection.performR_count]
theorem repair_cutFreeFirst : (repairFirst p f g).CutFree ↔ f.CutFree ∧ g.CutFree := by
  simp only [G.CutFree,repair_countFirst,Nat.add_eq_zero_iff]
theorem repair_atomizedFirst : (repairFirst p f g).Atomized ↔ f.Atomized ∧ g.Atomized := by
  simp only [repairFirst,G.Atomized,ContractionSelection.performR_atomized]
end First
section Second
variable (q : ContractionSelection C U L) (f : G P Γ (A::F)) (g : G P Θ (B::U))
def oldSecond : G P (Γ++Θ) (.conj A B::(F++L)) :=
  (ContractionSelection.fixed (.conj A B) (q.prependFixed F)).performR (Γ++Θ) (G.conjR f g)
def repairSecond : G P (Γ++Θ) (.conj A B::(F++L)) :=
  G.conjR f ((q.prependFixed [B]).performR Θ g)

theorem denoteSecond : ofTerm (repairSecond q f g).denote=ofTerm (oldSecond q f g).denote := by
  have hi : ofTerm ((Route.identity F).head A).coproduct=id (succ (A::F)) :=
    Route.identity_side .disj (A::F)
  have hm : ofTerm (repairSecond q f g).denote=
      ofTerm (Rules.conjRight (.comp f.denote ((Route.identity F).head A).coproduct)
        (.comp g.denote (q.route.head B).coproduct)) :=
    Rules.conjRight_congr (by rw [ofTerm_comp,hi,Laws.comp_id])
      ((q.prependFixed [B]).performR_denote Θ g)
  have ho : ofTerm (oldSecond q f g).denote=
      comp (ofTerm (G.conjR f g).denote) (ofTerm (((Route.identity F).parallel q.route).head (.conj A B)).coproduct) := by
    rw [oldSecond,ContractionSelection.performR_denote,←q.prepend_route F]
    rfl
  exact hm.trans ((Route.head_conjRight (Route.identity F) q.route f.denote g.denote).symm.trans ho.symm)

theorem old_countSecond : (oldSecond q f g).cutCount=f.cutCount+g.cutCount := by
  rw [oldSecond,ContractionSelection.performR_count]; rfl
theorem repair_countSecond : (repairSecond q f g).cutCount=f.cutCount+g.cutCount := by
  simp only [repairSecond,G.cutCount,ContractionSelection.performR_count]
theorem repair_cutFreeSecond : (repairSecond q f g).CutFree ↔ f.CutFree ∧ g.CutFree := by
  simp only [G.CutFree,repair_countSecond,Nat.add_eq_zero_iff]
theorem repair_atomizedSecond : (repairSecond q f g).Atomized ↔ f.Atomized ∧ g.Atomized := by
  simp only [repairSecond,G.Atomized,ContractionSelection.performR_atomized]
end Second
end W5.OneConjunction
end DosenPetric.Reduced.Gentzen
