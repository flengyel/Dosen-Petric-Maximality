module

public import DosenPetric.GentzenLogicalRetainedFactor
public import DosenPetric.GentzenRuleCongruence

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace Rules

theorem terminalDisjLeft_congr {F U Δ Λ : List (NormalForm P)} {A B : NormalForm P}
    {f f' : Term P (ante (F++[A])) (succ Δ)} {g g' : Term P (ante (U++[B])) (succ Λ)}
    (hf : ofTerm f=ofTerm f') (hg : ofTerm g=ofTerm g') :
    ofTerm (terminalDisjLeft f g)=ofTerm (terminalDisjLeft f' g') := by
  simp only [terminalDisjLeft,disjLeft,ofTerm_comp,ofTerm_tensor]
  rw [hf,hg]
end Rules

namespace W6.SourceLeft
variable {A B : NormalForm P} {F K U L Δ Λ : List (NormalForm P)}
variable (p : ContractionSelection (.disj A B) F K) (q : ContractionSelection (.disj A B) U L)
variable (f : G P (F++[A]) Δ) (g : G P (U++[B]) Λ)

def old : G P (p.erased++(q.erased++[.disj A B])) (Δ++Λ) :=
  (p.sourceOld q).performL (Δ++Λ) (BlockedSource.disjLLast f g)
def middle : G P ((K++L)++[.disj A B]) (Δ++Λ) :=
  BlockedSource.disjLLast ((p.extend [A]).performL Δ f) ((q.extend [B]).performL Λ g)
def repair : G P (p.erased++(q.erased++[.disj A B])) (Δ++Λ) :=
  (p.sourceRetained q).performL (Δ++Λ) (middle p q f g)

theorem denote : ofTerm (repair p q f g).denote=ofTerm (old p q f g).denote := by
  have hs := p.source_factor q .conj
  change ofTerm (p.sourceOld q).route.product =
    comp (ofTerm (p.sourceRetained q).route.product)
      (ofTerm ((p.route.parallel q.route).parallel (Route.identity [.disj A B])).product) at hs
  have hm : ofTerm (middle p q f g).denote =
      ofTerm (Rules.terminalDisjLeft
        (.comp (p.route.parallel (Route.identity [A])).product f.denote)
        (.comp (q.route.parallel (Route.identity [B])).product g.denote)) := by
    rw [middle,Rules.terminalDisjLeft_denote]
    apply Rules.terminalDisjLeft_congr
    · rw [ContractionSelection.performL_denote,p.extend_route]; rfl
    · rw [ContractionSelection.performL_denote,q.extend_route]; rfl
  rw [repair,old,ContractionSelection.performL_denote,ContractionSelection.performL_denote,
    hs,Laws.assoc,Rules.terminalDisjLeft_denote,hm,Rules.terminalDisjLeft_nat]

theorem old_count : (old p q f g).cutCount=f.cutCount+g.cutCount := by
  rw [old,ContractionSelection.performL_count,BlockedSource.disjLLast_count]
theorem repair_count : (repair p q f g).cutCount=f.cutCount+g.cutCount := by
  rw [repair,ContractionSelection.performL_count,middle,BlockedSource.disjLLast_count,
    ContractionSelection.performL_count,ContractionSelection.performL_count]
theorem old_cutFree : (old p q f g).CutFree ↔ f.CutFree ∧ g.CutFree := by
  simp only [G.CutFree,old_count,Nat.add_eq_zero_iff]
theorem repair_cutFree : (repair p q f g).CutFree ↔ f.CutFree ∧ g.CutFree := by
  simp only [G.CutFree,repair_count,Nat.add_eq_zero_iff]
theorem old_atomized : (old p q f g).Atomized ↔ f.Atomized ∧ g.Atomized := by
  simp only [old,ContractionSelection.performL_atomized,BlockedSource.disjLLast,G.atomized_reindex,G.Atomized]
theorem repair_atomized : (repair p q f g).Atomized ↔ f.Atomized ∧ g.Atomized := by
  simp only [repair,ContractionSelection.performL_atomized,middle,BlockedSource.disjLLast,G.atomized_reindex,G.Atomized]
theorem relation : (repair p q f g).relation=(old p q f g).relation := congrArg occurrenceMap (denote p q f g)

end W6.SourceLeft
end DosenPetric.Reduced.Gentzen
