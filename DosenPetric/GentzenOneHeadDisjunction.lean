module

public import DosenPetric.GentzenRetainedLastBlock
public import DosenPetric.GentzenParametricDisjunctionBounds

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace ContractionSelection
variable {C : NormalForm P} {F K : List (NormalForm P)}
variable (p : ContractionSelection C F K)

theorem retainedLast_source : gaps p.gs++p.tail++[C]++[]=p.erased++[C] := by
  rw [p.erased_eq]
  simp only [List.append_assoc,List.append_nil]
theorem retainedLast_target : gaps p.gs++[C]++p.tail++[]=K := by
  simpa only [List.append_assoc,List.singleton_append,List.append_nil] using p.lower

def retainedReturn {Δ : List (NormalForm P)} (f : G P (p.erased++[C]) Δ) : G P K Δ :=
  UnaryCast.exchangeL (gaps p.gs) p.tail [C] [] p.retainedLast_source p.retainedLast_target Δ f

theorem retainedReturn_denote {Δ : List (NormalForm P)} (f : G P (p.erased++[C]) Δ) :
    ofTerm (p.retainedReturn f).denote=comp (ofTerm p.retainedExit.product) (ofTerm f.denote) :=
  UnaryCast.exchangeL_denote _ _ _ _ _ _ _ _
end ContractionSelection
namespace W6.OneHeadDisjunction
variable {A B : NormalForm P} {F K U L Δ Λ : List (NormalForm P)}
section First
variable (p : ContractionSelection (.disj A B) F K) (f : G P (A::F) Δ) (g : G P (B::U) Λ)
abbrev blockFirst : ContractionBlock P ((K++U)++[.disj A B]) ((p.extend U).erased++[.disj A B]) where
  C:=.disj A B
  gs:=[gaps p.gs,p.tail++U]
  tail:=[]
  upper:=by
    have h:=(p.extend U).retainedLastBlock.upper
    change repeated (.disj A B) [gaps (p.extend U).gs,(p.extend U).tail]++[]=(K++U)++[.disj A B] at h
    rw [p.extend_gs,p.extend_tail] at h
    exact h
  lower:=by
    have h:=(p.extend U).retainedLastBlock.lower
    change gaps [gaps (p.extend U).gs,(p.extend U).tail]++.disj A B::[]=(p.extend U).erased++[.disj A B] at h
    rw [p.extend_gs,p.extend_tail] at h
    exact h

theorem block_eqFirst : blockFirst (U:=U) p=(p.extend U).retainedLastBlock := by
  apply ContractionBlock.ext_data
  · rfl
  · change [gaps p.gs,p.tail++U]=[gaps (p.extend U).gs,(p.extend U).tail]
    rw [p.extend_gs,p.extend_tail]
  · rfl

def oldFirst : G P (K++U) (Δ++Λ) := (ContractionSelection.more (p.extend U)).performL _ (G.disjL f g)
def innerFirst : G P (A::K) Δ := (p.prependFixed [A]).performL _ f
def bodyFirst : G P ((p.extend U).erased++[.disj A B]) (Δ++Λ) :=
  (p.extend U).retainedLastBlock.applyL ((p.extend U).retainedLast_bound) _
    (BlockedSource.disjLLast (BlockedSource.tailL A (innerFirst p f)) (BlockedSource.tailL B g))
def repairFirst : G P (K++U) (Δ++Λ) := (p.extend U).retainedReturn (bodyFirst p f g)

theorem blockedFirst : BlockedL (bodyFirst p f g) := by
  have h:=BlockedL.disjunctionFirst A B (gaps p.gs) p.tail U Δ Λ
    ((BlockedSource.tailL A (innerFirst p f)).reindex (congrArg (fun Ξ=>Ξ++[A]) p.lower.symm) rfl)
    (BlockedSource.tailL B g)
  have hm:=BlockedSource.disjLLast_reindex_inputs (BlockedSource.tailL A (innerFirst p f))
    (BlockedSource.tailL B g) p.lower.symm rfl
  have hl : gaps [gaps p.gs,p.tail++U]++[.disj A B]=(p.extend U).erased++[.disj A B] := (blockFirst p).lower
  have he:=h.reindex hl rfl
  unfold BlockedSource.left2 at he
  simp only [G.reindex_refl] at hm
  rw [hm] at he
  have hc : BlockedL ((blockFirst p).applyL (Nat.le_refl 2) _
      (BlockedSource.disjLLast (BlockedSource.tailL A (innerFirst p f)) (BlockedSource.tailL B g))) := by
    simpa only [ContractionBlock.applyL,blockFirst,G.reindex_trans] using he
  unfold bodyFirst
  rw [←ContractionBlock.applyL_congr (block_eqFirst (U:=U) p) (Nat.le_refl 2) (p.extend U).retainedLast_bound (Δ++Λ)
    (BlockedSource.disjLLast (BlockedSource.tailL A (innerFirst p f)) (BlockedSource.tailL B g))]
  exact hc

theorem denoteFirst : ofTerm (repairFirst p f g).denote=ofTerm (oldFirst p f g).denote := by
  have hs:=(p.extend U).retainedHead_square .conj
  change ofTerm (ContractionSelection.more (p.extend U)).route.product=
    comp (ofTerm (p.extend U).retainedHeadBlock.route.product)
      (ofTerm ((p.extend U).route.head (.disj A B)).product) at hs
  have hi : ofTerm ((Route.identity U).head B).product=id (ante (B::U)) := Route.identity_side .conj (B::U)
  have hm : ofTerm (G.disjL (innerFirst p f) g).denote=
      ofTerm (Rules.disjLeft (.comp (p.route.head A).product f.denote)
        (.comp ((Route.identity U).head B).product g.denote)) :=
    Rules.disjLeft_congr ((p.prependFixed [A]).performL_denote _ f) (by rw [ofTerm_comp,hi,Laws.id_comp])
  have hn:=hm.trans (Route.head_disjLeft p.route (Route.identity U) f.denote g.denote).symm
  rw [repairFirst,ContractionSelection.retainedReturn_denote,bodyFirst,ContractionBlock.denoteL,
    BlockedSource.disjLLast_native,←Laws.assoc,←Laws.assoc]
  rw [Laws.assoc (ofTerm (p.extend U).retainedExit.product),←ContractionSelection.retainedExit_product,hn,
    ←p.extend_route U,←Laws.assoc,←hs,oldFirst,ContractionSelection.performL_denote]
  rfl

theorem old_countFirst : (oldFirst p f g).cutCount=f.cutCount+g.cutCount := by
  rw [oldFirst,ContractionSelection.performL_count]; rfl
theorem repair_countFirst : (repairFirst p f g).cutCount=f.cutCount+g.cutCount := by
  simp only [repairFirst,ContractionSelection.retainedReturn,UnaryCast.exchangeL,G.count_reindex,G.cutCount,
    bodyFirst,ContractionBlock.countL,BlockedSource.disjLLast_count,BlockedSource.tailL,innerFirst,ContractionSelection.performL_count]
end First
section Second
variable (q : ContractionSelection (.disj A B) U L) (f : G P (A::F) Δ) (g : G P (B::U) Λ)
abbrev blockSecond : ContractionBlock P ((F++L)++[.disj A B]) ((q.prependFixed F).erased++[.disj A B]) where
  C:=.disj A B
  gs:=[F++gaps q.gs,q.tail]
  tail:=[]
  upper:=by
    have h:=(q.prependFixed F).retainedLastBlock.upper
    change repeated (.disj A B) [gaps (q.prependFixed F).gs,(q.prependFixed F).tail]++[]=(F++L)++[.disj A B] at h
    rw [q.gaps_prepend,ContractionSelection.tail_prependFixed] at h
    exact h
  lower:=by
    have h:=(q.prependFixed F).retainedLastBlock.lower
    change gaps [gaps (q.prependFixed F).gs,(q.prependFixed F).tail]++.disj A B::[]=(q.prependFixed F).erased++[.disj A B] at h
    rw [q.gaps_prepend,ContractionSelection.tail_prependFixed] at h
    exact h

theorem block_eqSecond : blockSecond (F:=F) q=(q.prependFixed F).retainedLastBlock := by
  apply ContractionBlock.ext_data
  · rfl
  · change [F++gaps q.gs,q.tail]=[gaps (q.prependFixed F).gs,(q.prependFixed F).tail]
    rw [q.gaps_prepend,ContractionSelection.tail_prependFixed]
  · rfl

def oldSecond : G P (F++L) (Δ++Λ) := (ContractionSelection.more (q.prependFixed F)).performL _ (G.disjL f g)
def innerSecond : G P (B::L) Λ := (q.prependFixed [B]).performL _ g
def bodySecond : G P ((q.prependFixed F).erased++[.disj A B]) (Δ++Λ) :=
  (q.prependFixed F).retainedLastBlock.applyL ((q.prependFixed F).retainedLast_bound) _
    (BlockedSource.disjLLast (BlockedSource.tailL A f) (BlockedSource.tailL B (innerSecond q g)))
def repairSecond : G P (F++L) (Δ++Λ) := (q.prependFixed F).retainedReturn (bodySecond q f g)

theorem blockedSecond : BlockedL (bodySecond q f g) := by
  have h:=BlockedL.disjunctionSecond A B F (gaps q.gs) q.tail Δ Λ
    (BlockedSource.tailL A f)
    ((BlockedSource.tailL B (innerSecond q g)).reindex (congrArg (fun Ξ=>Ξ++[B]) q.lower.symm) rfl)
  have hm:=BlockedSource.disjLLast_reindex_inputs (BlockedSource.tailL A f)
    (BlockedSource.tailL B (innerSecond q g)) rfl q.lower.symm
  have hl : gaps [F++gaps q.gs,q.tail]++[.disj A B]=(q.prependFixed F).erased++[.disj A B] := (blockSecond q).lower
  have he:=h.reindex hl rfl
  unfold BlockedSource.left2 at he
  simp only [G.reindex_refl] at hm
  rw [hm] at he
  have hc : BlockedL ((blockSecond q).applyL (Nat.le_refl 2) _
      (BlockedSource.disjLLast (BlockedSource.tailL A f) (BlockedSource.tailL B (innerSecond q g)))) := by
    simpa only [ContractionBlock.applyL,blockSecond,G.reindex_trans] using he
  unfold bodySecond
  rw [←ContractionBlock.applyL_congr (block_eqSecond (F:=F) q) (Nat.le_refl 2) (q.prependFixed F).retainedLast_bound (Δ++Λ)
    (BlockedSource.disjLLast (BlockedSource.tailL A f) (BlockedSource.tailL B (innerSecond q g)))]
  exact hc

theorem denoteSecond : ofTerm (repairSecond q f g).denote=ofTerm (oldSecond q f g).denote := by
  have hs:=(q.prependFixed F).retainedHead_square .conj
  change ofTerm (ContractionSelection.more (q.prependFixed F)).route.product=
    comp (ofTerm (q.prependFixed F).retainedHeadBlock.route.product)
      (ofTerm ((q.prependFixed F).route.head (.disj A B)).product) at hs
  have hi : ofTerm ((Route.identity F).head A).product=id (ante (A::F)) := Route.identity_side .conj (A::F)
  have hm : ofTerm (G.disjL f (innerSecond q g)).denote=
      ofTerm (Rules.disjLeft (.comp ((Route.identity F).head A).product f.denote)
        (.comp (q.route.head B).product g.denote)) :=
    Rules.disjLeft_congr (by rw [ofTerm_comp,hi,Laws.id_comp]) ((q.prependFixed [B]).performL_denote _ g)
  have hn:=hm.trans (Route.head_disjLeft (Route.identity F) q.route f.denote g.denote).symm
  rw [repairSecond,ContractionSelection.retainedReturn_denote,bodySecond,ContractionBlock.denoteL,
    BlockedSource.disjLLast_native,←Laws.assoc,←Laws.assoc]
  rw [Laws.assoc (ofTerm (q.prependFixed F).retainedExit.product),←ContractionSelection.retainedExit_product,hn,
    ←q.prepend_route F,←Laws.assoc,←hs,oldSecond,ContractionSelection.performL_denote]
  rfl

theorem old_countSecond : (oldSecond q f g).cutCount=f.cutCount+g.cutCount := by
  rw [oldSecond,ContractionSelection.performL_count]; rfl
theorem repair_countSecond : (repairSecond q f g).cutCount=f.cutCount+g.cutCount := by
  simp only [repairSecond,ContractionSelection.retainedReturn,UnaryCast.exchangeL,G.count_reindex,G.cutCount,
    bodySecond,ContractionBlock.countL,BlockedSource.disjLLast_count,BlockedSource.tailL,innerSecond,ContractionSelection.performL_count]
end Second
end W6.OneHeadDisjunction
end DosenPetric.Reduced.Gentzen
