module

public import DosenPetric.GentzenRetainedHeadBlock
public import DosenPetric.GentzenOneConjunction

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
theorem G.reindex_refl {Γ Δ : List (NormalForm P)} (g : G P Γ Δ) : g.reindex rfl rfl=g := rfl
namespace ContractionSelection
theorem gaps_prepend {C : NormalForm P} {F K : List (NormalForm P)}
    (p : ContractionSelection C F K) (Ξ : List (NormalForm P)) :
    gaps (p.prependFixed Ξ).gs=Ξ++gaps p.gs := by
  change (p.prependFixed Ξ).first++gaps (p.prependFixed Ξ).rest=Ξ++(p.first++gaps p.rest)
  rw [first_prependFixed,rest_prependFixed,List.append_assoc]
end ContractionSelection
namespace W6.OneHeadConjunction
variable {A B : NormalForm P} {F K U L Γ Θ : List (NormalForm P)}
section First
variable (p : ContractionSelection (.conj A B) F K)

abbrev blockFirst : ContractionBlock P (.conj A B::(K++U)) (K++U) where
  C := .conj A B
  gs := [[],gaps p.gs]
  tail := p.tail++U
  upper := by
    simpa only [repeated,List.nil_append,List.cons_append,List.append_assoc] using
      congrArg (List.cons (.conj A B)) (congrArg (fun Ξ => Ξ++U) p.lower)
  lower := by
    simpa only [gaps,List.nil_append,List.append_nil,List.cons_append,List.append_assoc] using
      congrArg (fun Ξ => Ξ++U) p.lower

theorem blockFirst_eq : blockFirst (U:=U) p=(p.extend U).retainedHeadBlock := by
  apply ContractionBlock.ext_data
  · rfl
  · change [[],gaps p.gs]=[[],gaps (p.extend U).gs]
    rw [p.extend_gs]
  · exact (p.extend_tail U).symm

variable (f : G P Γ (A::F)) (g : G P Θ (B::U))
def oldFirst : G P (Γ++Θ) (K++U) :=
  (ContractionSelection.more (p.extend U)).performR (Γ++Θ) (G.conjR f g)
def middleFirst : G P (Γ++Θ) (.conj A B::(K++U)) := G.conjR ((p.prependFixed [A]).performR Γ f) g
def repairFirst : G P (Γ++Θ) (K++U) := (blockFirst p).applyR (Nat.le_refl 2) _ (middleFirst p f g)

theorem denoteFirst : ofTerm (repairFirst p f g).denote=ofTerm (oldFirst p f g).denote := by
  have hs:=(p.extend U).retainedHead_square .disj
  rw [←blockFirst_eq,p.extend_route] at hs
  change ofTerm (ContractionSelection.more (p.extend U)).route.coproduct=
    comp (ofTerm ((p.route.parallel (Route.identity U)).head (.conj A B)).coproduct)
      (ofTerm (blockFirst p).route.coproduct) at hs
  have hi : ofTerm ((Route.identity U).head B).coproduct=id (succ (B::U)) := Route.identity_side .disj (B::U)
  have hm : ofTerm (middleFirst p f g).denote=
      ofTerm (Rules.conjRight (.comp f.denote (p.route.head A).coproduct)
        (.comp g.denote ((Route.identity U).head B).coproduct)) :=
    Rules.conjRight_congr ((p.prependFixed [A]).performR_denote Γ f)
      (by rw [ofTerm_comp,hi,Laws.comp_id])
  rw [repairFirst,ContractionBlock.denoteR,oldFirst,ContractionSelection.performR_denote,hs,←Laws.assoc]
  exact congrArg (fun k => comp k (ofTerm (blockFirst p).route.coproduct))
    (hm.trans (Route.head_conjRight p.route (Route.identity U) f.denote g.denote).symm)

theorem blockedFirst : BlockedR (repairFirst p f g) := by
  have h:=BlockedR.conjunctionFirst A B Γ Θ (gaps p.gs) p.tail U
    (((p.prependFixed [A]).performR Γ f).reindex rfl (congrArg (List.cons A) p.lower.symm)) g
  have hm:=G.conjR_reindex_inputs ((p.prependFixed [A]).performR Γ f) g p.lower.symm rfl
  simp only [G.reindex_refl] at hm
  have he:=h.reindex rfl (blockFirst (U:=U) p).lower
  unfold BlockedSource.right2 at he
  rw [hm] at he
  simpa only [repairFirst,ContractionBlock.applyR,blockFirst,G.reindex_trans,middleFirst] using he

theorem old_countFirst : (oldFirst p f g).cutCount=f.cutCount+g.cutCount := by
  rw [oldFirst,ContractionSelection.performR_count]; rfl
theorem repair_countFirst : (repairFirst p f g).cutCount=f.cutCount+g.cutCount := by
  simp only [repairFirst,ContractionBlock.countR,middleFirst,G.cutCount,ContractionSelection.performR_count]
end First
section Second
variable (q : ContractionSelection (.conj A B) U L)

abbrev blockSecond : ContractionBlock P (.conj A B::(F++L)) (F++L) where
  C := .conj A B
  gs := [[],F++gaps q.gs]
  tail := q.tail
  upper := by
    simpa only [repeated,List.nil_append,List.cons_append,List.append_assoc] using
      congrArg (List.cons (.conj A B)) (congrArg (fun Ξ => F++Ξ) q.lower)
  lower := by
    simpa only [gaps,List.nil_append,List.append_nil,List.cons_append,List.append_assoc] using
      congrArg (fun Ξ => F++Ξ) q.lower

theorem blockSecond_eq : blockSecond (F:=F) q=(q.prependFixed F).retainedHeadBlock := by
  apply ContractionBlock.ext_data
  · rfl
  · change [[],F++gaps q.gs]=[[],gaps (q.prependFixed F).gs]
    rw [q.gaps_prepend]
  · exact (ContractionSelection.tail_prependFixed F q).symm

variable (f : G P Γ (A::F)) (g : G P Θ (B::U))
def oldSecond : G P (Γ++Θ) (F++L) :=
  (ContractionSelection.more (q.prependFixed F)).performR (Γ++Θ) (G.conjR f g)
def middleSecond : G P (Γ++Θ) (.conj A B::(F++L)) := G.conjR f ((q.prependFixed [B]).performR Θ g)
def repairSecond : G P (Γ++Θ) (F++L) := (blockSecond q).applyR (Nat.le_refl 2) _ (middleSecond q f g)

theorem denoteSecond : ofTerm (repairSecond q f g).denote=ofTerm (oldSecond q f g).denote := by
  have hs:=(q.prependFixed F).retainedHead_square .disj
  rw [←blockSecond_eq,q.prepend_route] at hs
  change ofTerm (ContractionSelection.more (q.prependFixed F)).route.coproduct=
    comp (ofTerm (((Route.identity F).parallel q.route).head (.conj A B)).coproduct)
      (ofTerm (blockSecond q).route.coproduct) at hs
  have hi : ofTerm ((Route.identity F).head A).coproduct=id (succ (A::F)) := Route.identity_side .disj (A::F)
  have hm : ofTerm (middleSecond q f g).denote=
      ofTerm (Rules.conjRight (.comp f.denote ((Route.identity F).head A).coproduct)
        (.comp g.denote (q.route.head B).coproduct)) :=
    Rules.conjRight_congr (by rw [ofTerm_comp,hi,Laws.comp_id])
      ((q.prependFixed [B]).performR_denote Θ g)
  rw [repairSecond,ContractionBlock.denoteR,oldSecond,ContractionSelection.performR_denote,hs,←Laws.assoc]
  exact congrArg (fun k => comp k (ofTerm (blockSecond q).route.coproduct))
    (hm.trans (Route.head_conjRight (Route.identity F) q.route f.denote g.denote).symm)

theorem blockedSecond : BlockedR (repairSecond q f g) := by
  have h:=BlockedR.conjunctionSecond A B Γ Θ F (gaps q.gs) q.tail f
    (((q.prependFixed [B]).performR Θ g).reindex rfl (congrArg (List.cons B) q.lower.symm))
  have hm:=G.conjR_reindex_inputs f ((q.prependFixed [B]).performR Θ g) rfl q.lower.symm
  simp only [G.reindex_refl] at hm
  have he:=h.reindex rfl (blockSecond (F:=F) q).lower
  unfold BlockedSource.right2 at he
  rw [hm] at he
  simpa only [repairSecond,ContractionBlock.applyR,blockSecond,G.reindex_trans,middleSecond] using he

theorem old_countSecond : (oldSecond q f g).cutCount=f.cutCount+g.cutCount := by
  rw [oldSecond,ContractionSelection.performR_count]; rfl
theorem repair_countSecond : (repairSecond q f g).cutCount=f.cutCount+g.cutCount := by
  simp only [repairSecond,ContractionBlock.countR,middleSecond,G.cutCount,ContractionSelection.performR_count]
end Second
end W6.OneHeadConjunction
end DosenPetric.Reduced.Gentzen
