module

public import DosenPetric.GentzenTerminalSelectionFactor

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.W6.TerminalOne
universe u
variable {P : Type u} {A B : NormalForm P} {F K U L Δ Λ : List (NormalForm P)}
section First
variable (p : ContractionSelection (.disj A B) F K) (f : G P (F++[A]) Δ) (g : G P (U++[B]) Λ)

def oldFirst : G P ((p.extend U).erased++[.disj A B]) (Δ++Λ) :=
  ((p.extend U).chain (.last [])).performL _ (BlockedSource.disjLLast f g)
def innerFirst : G P (K++[A]) Δ := (p.extend [A]).performL _ f
def middleFirst : G P ((K++U)++[.disj A B]) (Δ++Λ) := BlockedSource.disjLLast (innerFirst p f) g
def repairFirst : G P ((p.extend U).erased++[.disj A B]) (Δ++Λ) :=
  (p.extend U).retainedLastBlock.applyL (p.extend U).retainedLast_bound _ (middleFirst p f g)

theorem endpointFirst : (p.extend U).erased++[.disj A B]=(p.erased++U)++[.disj A B] :=
  congrArg (fun Ξ=>Ξ++[.disj A B]) (p.extend_erased U)

theorem blockedFirst : BlockedL (repairFirst p f g) := SourceOne.blockedFirst p _ g

theorem denoteFirst : ofTerm (repairFirst p f g).denote=ofTerm (oldFirst p f g).denote := by
  have hs:=(p.extend U).terminal_factor .conj
  rw [p.extend_route U] at hs
  change ofTerm ((p.extend U).chain (.last [])).route.product=comp
    (ofTerm (p.extend U).retainedLastBlock.route.product)
    (ofTerm (((p.route.parallel (Route.identity U)).parallel (Route.identity [.disj A B])).product)) at hs
  have hm : ofTerm (middleFirst p f g).denote=ofTerm (Rules.terminalDisjLeft
      (.comp (p.route.parallel (Route.identity [A])).product f.denote)
      (.comp ((Route.identity U).parallel (Route.identity [B])).product g.denote)) := by
    rw [middleFirst,Rules.terminalDisjLeft_denote]
    apply Rules.terminalDisjLeft_congr
    · rw [innerFirst,ContractionSelection.performL_denote,p.extend_route]; rfl
    · rw [ofTerm_comp,Route.identity_parallel]
      have hi : ofTerm (Route.identity (U++[B])).product=id (ante (U++[B])) := Route.identity_side .conj (U++[B])
      rw [hi,Laws.id_comp]
  rw [repairFirst,ContractionBlock.denoteL,oldFirst,ContractionSelection.performL_denote,hs,Laws.assoc,
    Rules.terminalDisjLeft_denote,hm,Rules.terminalDisjLeft_nat]

theorem old_countFirst : (oldFirst p f g).cutCount=f.cutCount+g.cutCount := by
  rw [oldFirst,ContractionSelection.performL_count,BlockedSource.disjLLast_count]
theorem repair_countFirst : (repairFirst p f g).cutCount=f.cutCount+g.cutCount := by
  rw [repairFirst,ContractionBlock.countL,middleFirst,BlockedSource.disjLLast_count,innerFirst,ContractionSelection.performL_count]
theorem cutFreeFirst : (repairFirst p f g).CutFree↔(oldFirst p f g).CutFree := by
  simp only [G.CutFree,repair_countFirst,old_countFirst]
theorem old_atomizedFirst : (oldFirst p f g).Atomized↔f.Atomized∧g.Atomized := by
  simp only [oldFirst,ContractionSelection.performL_atomized,BlockedSource.disjLLast,G.atomized_reindex,G.Atomized]
theorem repair_atomizedFirst : (repairFirst p f g).Atomized↔f.Atomized∧g.Atomized := by
  simp only [repairFirst,ContractionBlock.atomizedL,middleFirst,BlockedSource.disjLLast,G.atomized_reindex,G.Atomized,innerFirst,ContractionSelection.performL_atomized]
theorem relationFirst : (repairFirst p f g).relation=(oldFirst p f g).relation := congrArg occurrenceMap (denoteFirst p f g)
end First
section Second
variable (q : ContractionSelection (.disj A B) U L) (f : G P (F++[A]) Δ) (g : G P (U++[B]) Λ)

def oldSecond : G P ((q.prependFixed F).erased++[.disj A B]) (Δ++Λ) :=
  ((q.prependFixed F).chain (.last [])).performL _ (BlockedSource.disjLLast f g)
def innerSecond : G P (L++[B]) Λ := (q.extend [B]).performL _ g
def middleSecond : G P ((F++L)++[.disj A B]) (Δ++Λ) := BlockedSource.disjLLast f (innerSecond q g)
def repairSecond : G P ((q.prependFixed F).erased++[.disj A B]) (Δ++Λ) :=
  (q.prependFixed F).retainedLastBlock.applyL (q.prependFixed F).retainedLast_bound _ (middleSecond q f g)

theorem endpointSecond : (q.prependFixed F).erased++[.disj A B]=(F++q.erased)++[.disj A B] :=
  congrArg (fun Ξ=>Ξ++[.disj A B]) (q.prepend_erased F)

theorem blockedSecond : BlockedL (repairSecond q f g) := SourceOne.blockedSecond q f _

theorem denoteSecond : ofTerm (repairSecond q f g).denote=ofTerm (oldSecond q f g).denote := by
  have hs:=(q.prependFixed F).terminal_factor .conj
  rw [q.prepend_route F] at hs
  change ofTerm ((q.prependFixed F).chain (.last [])).route.product=comp
    (ofTerm (q.prependFixed F).retainedLastBlock.route.product)
    (ofTerm ((((Route.identity F).parallel q.route).parallel (Route.identity [.disj A B])).product)) at hs
  have hm : ofTerm (middleSecond q f g).denote=ofTerm (Rules.terminalDisjLeft
      (.comp ((Route.identity F).parallel (Route.identity [A])).product f.denote)
      (.comp (q.route.parallel (Route.identity [B])).product g.denote)) := by
    rw [middleSecond,Rules.terminalDisjLeft_denote]
    apply Rules.terminalDisjLeft_congr
    · rw [ofTerm_comp,Route.identity_parallel]
      have hi : ofTerm (Route.identity (F++[A])).product=id (ante (F++[A])) := Route.identity_side .conj (F++[A])
      rw [hi,Laws.id_comp]
    · rw [innerSecond,ContractionSelection.performL_denote,q.extend_route]; rfl
  rw [repairSecond,ContractionBlock.denoteL,oldSecond,ContractionSelection.performL_denote,hs,Laws.assoc,
    Rules.terminalDisjLeft_denote,hm,Rules.terminalDisjLeft_nat]

theorem old_countSecond : (oldSecond q f g).cutCount=f.cutCount+g.cutCount := by
  rw [oldSecond,ContractionSelection.performL_count,BlockedSource.disjLLast_count]
theorem repair_countSecond : (repairSecond q f g).cutCount=f.cutCount+g.cutCount := by
  rw [repairSecond,ContractionBlock.countL,middleSecond,BlockedSource.disjLLast_count,innerSecond,ContractionSelection.performL_count]
theorem cutFreeSecond : (repairSecond q f g).CutFree↔(oldSecond q f g).CutFree := by
  simp only [G.CutFree,repair_countSecond,old_countSecond]
theorem old_atomizedSecond : (oldSecond q f g).Atomized↔f.Atomized∧g.Atomized := by
  simp only [oldSecond,ContractionSelection.performL_atomized,BlockedSource.disjLLast,G.atomized_reindex,G.Atomized]
theorem repair_atomizedSecond : (repairSecond q f g).Atomized↔f.Atomized∧g.Atomized := by
  simp only [repairSecond,ContractionBlock.atomizedL,middleSecond,BlockedSource.disjLLast,G.atomized_reindex,G.Atomized,innerSecond,ContractionSelection.performL_atomized]
theorem relationSecond : (repairSecond q f g).relation=(oldSecond q f g).relation := congrArg occurrenceMap (denoteSecond q f g)
end Second
end DosenPetric.Reduced.Gentzen.W6.TerminalOne
