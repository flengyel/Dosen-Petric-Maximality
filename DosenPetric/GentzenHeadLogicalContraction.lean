module

public import DosenPetric.GentzenSelectedHeadBlock
public import DosenPetric.GentzenHeadLogicalNaturality
public import DosenPetric.GentzenRuleCongruence

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace ContractionSelection
variable {C : NormalForm P} {F K U L : List (NormalForm P)}
variable (p : ContractionSelection C F K) (q : ContractionSelection C U L)

theorem chain_get {A : NormalForm P} (a : At (F++U) A) :
    (p.chain q).route.get a=(p.mergeBlock q).route.get ((p.route.parallel q.route).get a) := by
  rw [←p.merge_route q]
  cases At.cases_append F U a with
  | inl h => obtain ⟨a,rfl⟩:=h; rw [chain_before,Route.parallel_before]
  | inr h => obtain ⟨a,rfl⟩:=h; rw [chain_shift,Route.parallel_shift,merge_shift]

theorem head_chain_square (o : Op) :
    (more (p.chain q)).route.sideArrow o=(side P o).comp
      ((p.mergeBlock q).selectedHead.route.sideArrow o)
      (((p.route.parallel q.route).head C).sideArrow o) := by
  apply side_ext o
  intro A a
  rw [(side P o).assoc,Route.sideArrow_get,Route.sideArrow_get,Route.sideArrow_get]
  apply congrArg (component o)
  rw [ContractionBlock.selectedHead_route]
  cases a with
  | here => exact (p.merge_retained q).symm
  | there a => simpa only [route,Route.head,Route.get,Route.get_map] using p.chain_get q a
end ContractionSelection

namespace W6.HeadRight
variable {A B : NormalForm P} {F K U L Γ Θ : List (NormalForm P)}
variable (p : ContractionSelection (.conj A B) F K) (q : ContractionSelection (.conj A B) U L)
variable (f : G P Γ (A::F)) (g : G P Θ (B::U))

def old : G P (Γ++Θ) (p.erased++L) :=
  (ContractionSelection.more (p.chain q)).performR (Γ++Θ) (G.conjR f g)
def middle : G P (Γ++Θ) (.conj A B::(K++L)) :=
  G.conjR ((p.prependFixed [A]).performR Γ f) ((q.prependFixed [B]).performR Θ g)

theorem middle_bound : 2≤(p.mergeBlock q).selectedHead.gs.length := by change 2≤3; decide

def repair : G P (Γ++Θ) (p.erased++L) :=
  (p.mergeBlock q).selectedHead.applyR (middle_bound p q) _ (middle p q f g)

theorem denote : ofTerm (repair p q f g).denote=ofTerm (old p q f g).denote := by
  have hs:=p.head_chain_square q .disj
  change ofTerm (ContractionSelection.more (p.chain q)).route.coproduct=
    comp (ofTerm ((p.route.parallel q.route).head (.conj A B)).coproduct)
      (ofTerm (p.mergeBlock q).selectedHead.route.coproduct) at hs
  have hm : ofTerm (middle p q f g).denote=
      ofTerm (Rules.conjRight (.comp f.denote (p.route.head A).coproduct)
        (.comp g.denote (q.route.head B).coproduct)) :=
    Rules.conjRight_congr ((p.prependFixed [A]).performR_denote Γ f)
      ((q.prependFixed [B]).performR_denote Θ g)
  rw [repair,ContractionBlock.denoteR,old,ContractionSelection.performR_denote,
    hs,←Laws.assoc]
  exact congrArg (fun k => comp k (ofTerm (p.mergeBlock q).selectedHead.route.coproduct))
    (hm.trans (Route.head_conjRight p.route q.route f.denote g.denote).symm)

end W6.HeadRight
end DosenPetric.Reduced.Gentzen
