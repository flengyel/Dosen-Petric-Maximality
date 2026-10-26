module

public import DosenPetric.GentzenSelectedTerminalSquare

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.SelectedLogicalReducer
universe u
variable {P : Type u} {A B : NormalForm P} {Γ Θ K L Δ : List (NormalForm P)}

section Left
variable (g : SelectionMask (.conj A B) Γ) (t : SelectionMask (.conj A B) Θ)
variable (q : ContractionSelection (.conj A B) (Γ++.conj A B::Θ) K)
variable (p : ContractionSelection (.conj A B) (Γ++Θ) L)
variable (hq : q.mask=SelectionMask.selectedContext g t) (hp : p.mask=g.append t)

def repairL (f : G P (Γ++A::B::Θ) Δ) : G P K Δ :=
  (exit g t q p hq hp).left (sourceRepairL p (G.moveEndL Γ [A,B] Θ Δ f))

theorem countL (f : G P (Γ++A::B::Θ) Δ) : (repairL g t q p hq hp f).cutCount=f.cutCount := by
  rw [repairL,ExchangeScript.left_count,sourceCountL,G.moveEndL_count]

theorem denoteL (f : G P (Γ++A::B::Θ) Δ) :
    ofTerm (repairL g t q p hq hp f).denote=ofTerm (q.performL Δ (G.conjL Γ Θ Δ A B f)).denote := by
  rw [repairL,ExchangeScript.left_denote,sourceDenoteL,ContractionSelection.performL_denote]
  change comp ((exit g t q p hq hp).arrow .conj)
    (comp (ofTerm (terminal p).route.product)
      (comp (ofTerm (Rules.conjLeft (Γ++Θ) [] A B).toTerm) (ofTerm (G.moveEndL Γ [A,B] Θ Δ f).denote)))=_
  rw [G.moveEndL_denote,ContractionSelection.performL_denote]
  change comp ((exit g t q p hq hp).arrow .conj)
    (comp (ofTerm (terminal p).route.product)
      (comp (ofTerm (Rules.conjLeft (Γ++Θ) [] A B).toTerm)
        (comp (ofTerm (Route.moveEnd Γ [A,B] Θ).product) (ofTerm f.denote))))=
    comp (ofTerm q.route.product) (comp (ofTerm (Rules.conjLeft Γ Θ A B).toTerm) (ofTerm f.denote))
  rw [conjLeft_compare,conjLeft_compare]
  let d : (side P .conj).Hom (ante (Γ++A::B::Θ)) (succ Δ):=ofTerm f.denote
  change (side P .conj).comp ((exit g t q p hq hp).arrow .conj)
      ((side P .conj).comp ((terminal p).route.sideArrow .conj)
        ((side P .conj).comp (logicalSide .conj (Γ++Θ) [] A B)
          ((side P .conj).comp ((Route.moveEnd Γ [A,B] Θ).sideArrow .conj) d)))=
    (side P .conj).comp (q.route.sideArrow .conj) ((side P .conj).comp (logicalSide .conj Γ Θ A B) d)
  symm
  simpa only [(side P .conj).assoc] using congrArg (fun f=>(side P .conj).comp f d)
    (logical_terminal_side .conj A B g t q p hq hp)

theorem boundL (f : G P (Γ++A::B::Θ) Δ) (hn : 2≤q.arity) :
    ContractionBound .left (.conj A B) ((q.performL Δ (G.conjL Γ Θ Δ A B f)).rho .left q.keep)
      (repairL g t q p hq hp f) (fun a=>a=q.keep) := by
  have h:=(sourceBoundL p (G.moveEndL Γ [A,B] Θ Δ f)).weaken
    (source_thresholdL g t q p hq hp f hn)
  apply (exit g t q p hq hp).bound_left
  apply h.mono
  intro a ha
  have he : a=(terminal p).keep :=
    (exit g t q p hq hp).injective a _ (ha.trans (exit_keep g t q p hq hp).symm)
  cases he
  exact source_keep_index .conj A B p
end Left

section Right
variable (g : SelectionMask (.disj A B) Γ) (t : SelectionMask (.disj A B) Θ)
variable (q : ContractionSelection (.disj A B) (Γ++.disj A B::Θ) K)
variable (p : ContractionSelection (.disj A B) (Γ++Θ) L)
variable (hq : q.mask=SelectionMask.selectedContext g t) (hp : p.mask=g.append t)

def repairR (f : G P Δ (Γ++A::B::Θ)) : G P Δ K :=
  (exit g t q p hq hp).right (sourceRepairR p (G.moveEndR Δ Γ [A,B] Θ f))

theorem countR (f : G P Δ (Γ++A::B::Θ)) : (repairR g t q p hq hp f).cutCount=f.cutCount := by
  rw [repairR,ExchangeScript.right_count,sourceCountR,G.moveEndR_count]

theorem denoteR (f : G P Δ (Γ++A::B::Θ)) :
    ofTerm (repairR g t q p hq hp f).denote=ofTerm (q.performR Δ (G.disjR Δ Γ Θ A B f)).denote := by
  rw [repairR,ExchangeScript.right_denote,sourceDenoteR,ContractionSelection.performR_denote]
  change comp
    (comp (comp (ofTerm (G.moveEndR Δ Γ [A,B] Θ f).denote)
      (ofTerm (Rules.disjRight (Γ++Θ) [] A B).toTerm)) (ofTerm (terminal p).route.coproduct))
    ((exit g t q p hq hp).arrow .disj)=_
  rw [G.moveEndR_denote,ContractionSelection.performR_denote]
  change comp
    (comp (comp (comp (ofTerm f.denote) (ofTerm (Route.moveEnd Γ [A,B] Θ).coproduct))
      (ofTerm (Rules.disjRight (Γ++Θ) [] A B).toTerm)) (ofTerm (terminal p).route.coproduct))
    ((exit g t q p hq hp).arrow .disj)=
    comp (comp (ofTerm f.denote) (ofTerm (Rules.disjRight Γ Θ A B).toTerm)) (ofTerm q.route.coproduct)
  rw [disjRight_compare,disjRight_compare]
  let d : (side P .disj).Hom (succ (Γ++A::B::Θ)) (ante Δ):=ofTerm f.denote
  change (side P .disj).comp ((exit g t q p hq hp).arrow .disj)
      ((side P .disj).comp ((terminal p).route.sideArrow .disj)
        ((side P .disj).comp (logicalSide .disj (Γ++Θ) [] A B)
          ((side P .disj).comp ((Route.moveEnd Γ [A,B] Θ).sideArrow .disj) d)))=
    (side P .disj).comp (q.route.sideArrow .disj) ((side P .disj).comp (logicalSide .disj Γ Θ A B) d)
  symm
  simpa only [(side P .disj).assoc] using congrArg (fun f=>(side P .disj).comp f d)
    (logical_terminal_side .disj A B g t q p hq hp)

theorem boundR (f : G P Δ (Γ++A::B::Θ)) (hn : 2≤q.arity) :
    ContractionBound .right (.disj A B) ((q.performR Δ (G.disjR Δ Γ Θ A B f)).rho .right q.keep)
      (repairR g t q p hq hp f) (fun a=>a=q.keep) := by
  have h:=(sourceBoundR p (G.moveEndR Δ Γ [A,B] Θ f)).weaken
    (source_thresholdR g t q p hq hp f hn)
  apply (exit g t q p hq hp).bound_right
  apply h.mono
  intro a ha
  have he : a=(terminal p).keep :=
    (exit g t q p hq hp).injective a _ (ha.trans (exit_keep g t q p hq hp).symm)
  cases he
  exact source_keep_index .disj A B p
end Right
end DosenPetric.Reduced.Gentzen.SelectedLogicalReducer
