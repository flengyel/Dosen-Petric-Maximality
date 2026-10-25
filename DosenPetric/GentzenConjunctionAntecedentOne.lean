module

public import DosenPetric.GentzenConjunctionAntecedentBoth

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.W5.OneConjunctionAntecedent
universe u
variable {P : Type u} {A B C : NormalForm P} {F K U L Δ Λ : List (NormalForm P)}
section First
variable (p : ContractionSelection C F K) (f : G P F (A::Δ)) (g : G P U (B::Λ))
def oldFirst : G P (K++U) (.conj A B::(Δ++Λ)) := (p.extend U).performL _ (G.conjR f g)
def repairFirst : G P (K++U) (.conj A B::(Δ++Λ)) := G.conjR (p.performL _ f) g

theorem denoteFirst : ofTerm (repairFirst p f g).denote=ofTerm (oldFirst p f g).denote := by
  have hi : ofTerm (Route.identity U).product=id (ante U) := Route.identity_side .conj U
  have hm : ofTerm (repairFirst p f g).denote=
      ofTerm (Rules.conjRight (.comp p.route.product f.denote) (.comp (Route.identity U).product g.denote)) :=
    Rules.conjRight_congr (p.performL_denote _ f) (by rw [ofTerm_comp,hi,Laws.id_comp])
  have ho : ofTerm (oldFirst p f g).denote=
      comp (ofTerm (p.route.parallel (Route.identity U)).product) (ofTerm (G.conjR f g).denote) := by
    rw [oldFirst,ContractionSelection.performL_denote,p.extend_route]
  exact hm.trans ((Route.parallel_conjRight p.route (Route.identity U) f.denote g.denote).symm.trans ho.symm)

theorem old_countFirst : (oldFirst p f g).cutCount=f.cutCount+g.cutCount := by
  rw [oldFirst,ContractionSelection.performL_count]; rfl
theorem repair_countFirst : (repairFirst p f g).cutCount=f.cutCount+g.cutCount := by
  simp only [repairFirst,G.cutCount,ContractionSelection.performL_count]

theorem old_rankFirst : (oldFirst p f g).rho .left (p.keep.before U)=
    (p.selected.map (fun a => f.rho .left a)).sum+p.arity+(if 2≤p.arity then 1 else 0) := by
  let R : At (K++U) C→Nat := fun a => (oldFirst p f g).rho .left a
  let r : At (F++U) C→Nat := fun a => (G.conjR f g).rho .left a
  have h:=(p.extend U).performL_rank _ (G.conjR f g)
  change R (p.extend U).keep=((p.extend U).selected.map r).sum+(if 2≤(p.extend U).arity then 1 else 0) at h
  rw [p.extend_keep,p.extend_selected,p.extend_arity] at h
  simp only [List.map_map,Function.comp_def] at h
  change (oldFirst p f g).rho .left (p.keep.before U)=
    (p.selected.map (fun a => (G.conjR f g).rho .left (a.before U))).sum+(if 2≤p.arity then 1 else 0) at h
  simp only [G.rho_conjR_f_left] at h
  let rf : At F C→Nat := fun a => f.rho .left a
  change R (p.keep.before U)=(p.selected.map (fun a => 1+rf a)).sum+(if 2≤p.arity then 1 else 0) at h
  rw [G.sum_map_one_add,p.selected_length] at h
  change R (p.keep.before U)=(p.selected.map rf).sum+p.arity+(if 2≤p.arity then 1 else 0)
  omega

theorem repair_rankFirst : (repairFirst p f g).rho .left (p.keep.before U)=
    1+(p.selected.map (fun a => f.rho .left a)).sum+(if 2≤p.arity then 1 else 0) := by
  have h:=G.rho_conjR_f_left (p.performL _ f) g p.keep
  have hc:=congrArg (fun n => 1+n) (p.performL_rank _ f)
  change (repairFirst p f g).rho .left (p.keep.before U)=_ at h
  omega

theorem endpoint_ltFirst (hn : 2≤p.arity) :
    (repairFirst p f g).rho .left (p.keep.before U)<(oldFirst p f g).rho .left (p.keep.before U) := by
  rw [repair_rankFirst,old_rankFirst]; omega

theorem reducesFirst {Φ Ξ Ω Ψ : List (NormalForm P)} (hn : 2≤p.arity)
    (cutLeft : G P Φ (C::Ξ)) (root : G P (C::Ω) Ψ) :
    ReducesL cutLeft root (oldFirst p f g) (p.keep.before U) := by
  intro a hr
  refine ⟨repairFirst p f g,?_,denoteFirst p f g,?_⟩
  · have hc:=hr.cutFree
    change (oldFirst p f g).cutCount=0 at hc
    rw [old_countFirst] at hc
    change (repairFirst p f g).cutCount=0
    rw [repair_countFirst]; exact hc
  · intro I J v b y hv
    exact ReducibilityBoundary.strict_left a _ hr (endpoint_ltFirst p f g hn) b y hv
end First
section Second
variable (q : ContractionSelection C U L) (f : G P F (A::Δ)) (g : G P U (B::Λ))
def oldSecond : G P (F++L) (.conj A B::(Δ++Λ)) := (q.prependFixed F).performL _ (G.conjR f g)
def repairSecond : G P (F++L) (.conj A B::(Δ++Λ)) := G.conjR f (q.performL _ g)

theorem denoteSecond : ofTerm (repairSecond q f g).denote=ofTerm (oldSecond q f g).denote := by
  have hi : ofTerm (Route.identity F).product=id (ante F) := Route.identity_side .conj F
  have hm : ofTerm (repairSecond q f g).denote=
      ofTerm (Rules.conjRight (.comp (Route.identity F).product f.denote) (.comp q.route.product g.denote)) :=
    Rules.conjRight_congr (by rw [ofTerm_comp,hi,Laws.id_comp]) (q.performL_denote _ g)
  have ho : ofTerm (oldSecond q f g).denote=
      comp (ofTerm ((Route.identity F).parallel q.route).product) (ofTerm (G.conjR f g).denote) := by
    rw [oldSecond,ContractionSelection.performL_denote,q.prepend_route]
  exact hm.trans ((Route.parallel_conjRight (Route.identity F) q.route f.denote g.denote).symm.trans ho.symm)

theorem old_countSecond : (oldSecond q f g).cutCount=f.cutCount+g.cutCount := by
  rw [oldSecond,ContractionSelection.performL_count]; rfl
theorem repair_countSecond : (repairSecond q f g).cutCount=f.cutCount+g.cutCount := by
  simp only [repairSecond,G.cutCount,ContractionSelection.performL_count]

theorem old_rankSecond : (oldSecond q f g).rho .left (At.shift F q.keep)=
    (q.selected.map (fun a => g.rho .left a)).sum+q.arity+(if 2≤q.arity then 1 else 0) := by
  let R : At (F++L) C→Nat := fun a => (oldSecond q f g).rho .left a
  let r : At (F++U) C→Nat := fun a => (G.conjR f g).rho .left a
  have h:=(q.prependFixed F).performL_rank _ (G.conjR f g)
  change R (q.prependFixed F).keep=((q.prependFixed F).selected.map r).sum+
    (if 2≤(q.prependFixed F).arity then 1 else 0) at h
  rw [q.prepend_keep,q.prepend_selected,q.prepend_arity] at h
  simp only [List.map_map,Function.comp_def] at h
  change (oldSecond q f g).rho .left (At.shift F q.keep)=
    (q.selected.map (fun a => (G.conjR f g).rho .left (At.shift F a))).sum+(if 2≤q.arity then 1 else 0) at h
  simp only [G.rho_conjR_g_left] at h
  let rg : At U C→Nat := fun a => g.rho .left a
  change R (At.shift F q.keep)=(q.selected.map (fun a => 1+rg a)).sum+(if 2≤q.arity then 1 else 0) at h
  rw [G.sum_map_one_add,q.selected_length] at h
  change R (At.shift F q.keep)=(q.selected.map rg).sum+q.arity+(if 2≤q.arity then 1 else 0)
  omega

theorem repair_rankSecond : (repairSecond q f g).rho .left (At.shift F q.keep)=
    1+(q.selected.map (fun a => g.rho .left a)).sum+(if 2≤q.arity then 1 else 0) := by
  have h:=G.rho_conjR_g_left f (q.performL _ g) q.keep
  have hc:=congrArg (fun n => 1+n) (q.performL_rank _ g)
  change (repairSecond q f g).rho .left (At.shift F q.keep)=_ at h
  omega

theorem endpoint_ltSecond (hn : 2≤q.arity) :
    (repairSecond q f g).rho .left (At.shift F q.keep)<(oldSecond q f g).rho .left (At.shift F q.keep) := by
  rw [repair_rankSecond,old_rankSecond]; omega

theorem reducesSecond {Φ Ξ Ω Ψ : List (NormalForm P)} (hn : 2≤q.arity)
    (cutLeft : G P Φ (C::Ξ)) (root : G P (C::Ω) Ψ) :
    ReducesL cutLeft root (oldSecond q f g) (At.shift F q.keep) := by
  intro a hr
  refine ⟨repairSecond q f g,?_,denoteSecond q f g,?_⟩
  · have hc:=hr.cutFree
    change (oldSecond q f g).cutCount=0 at hc
    rw [old_countSecond] at hc
    change (repairSecond q f g).cutCount=0
    rw [repair_countSecond]; exact hc
  · intro I J v b y hv
    exact ReducibilityBoundary.strict_left a _ hr (endpoint_ltSecond q f g hn) b y hv
end Second
end DosenPetric.Reduced.Gentzen.W5.OneConjunctionAntecedent
