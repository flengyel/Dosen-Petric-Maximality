module

public import DosenPetric.GentzenDisjunctionSuccedentBounds

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.W5.OneDisjunctionSuccedent
universe u
variable {P : Type u} {A B C : NormalForm P} {F K U L Γ Θ : List (NormalForm P)}
section First
variable (p : ContractionSelection C F K) (f : G P (A::Γ) F) (g : G P (B::Θ) U)
def oldFirst : G P (.disj A B::(Γ++Θ)) (K++U) := (p.extend U).performR _ (G.disjL f g)
def repairFirst : G P (.disj A B::(Γ++Θ)) (K++U) := G.disjL (p.performR _ f) g

theorem denoteFirst : ofTerm (repairFirst p f g).denote=ofTerm (oldFirst p f g).denote := by
  have hi : ofTerm (Route.identity U).coproduct=id (succ U) := Route.identity_side .disj U
  have hm : ofTerm (repairFirst p f g).denote=
      ofTerm (Rules.disjLeft (.comp f.denote p.route.coproduct) (.comp g.denote (Route.identity U).coproduct)) :=
    Rules.disjLeft_congr (p.performR_denote _ f) (by rw [ofTerm_comp,hi,Laws.comp_id])
  have ho : ofTerm (oldFirst p f g).denote=
      comp (ofTerm (G.disjL f g).denote) (ofTerm (p.route.parallel (Route.identity U)).coproduct) := by
    rw [oldFirst,ContractionSelection.performR_denote,p.extend_route]
  exact hm.trans ((Route.parallel_disjLeft p.route (Route.identity U) f.denote g.denote).symm.trans ho.symm)

theorem old_countFirst : (oldFirst p f g).cutCount=f.cutCount+g.cutCount := by
  rw [oldFirst,ContractionSelection.performR_count]; rfl
theorem repair_countFirst : (repairFirst p f g).cutCount=f.cutCount+g.cutCount := by
  simp only [repairFirst,G.cutCount,ContractionSelection.performR_count]

theorem old_rankFirst : (oldFirst p f g).rho .right (p.keep.before U)=
    (p.selected.map (fun a => f.rho .right a)).sum+p.arity+(if 2≤p.arity then 1 else 0) := by
  let R : At (K++U) C→Nat := fun a => (oldFirst p f g).rho .right a
  let r : At (F++U) C→Nat := fun a => (G.disjL f g).rho .right a
  have h:=(p.extend U).performR_rank _ (G.disjL f g)
  change R (p.extend U).keep=((p.extend U).selected.map r).sum+(if 2≤(p.extend U).arity then 1 else 0) at h
  rw [p.extend_keep,p.extend_selected,p.extend_arity] at h
  simp only [List.map_map,Function.comp_def] at h
  change (oldFirst p f g).rho .right (p.keep.before U)=
    (p.selected.map (fun a => (G.disjL f g).rho .right (a.before U))).sum+(if 2≤p.arity then 1 else 0) at h
  simp only [G.rho_disjL_f_right] at h
  let rf : At F C→Nat := fun a => f.rho .right a
  change R (p.keep.before U)=(p.selected.map (fun a => 1+rf a)).sum+(if 2≤p.arity then 1 else 0) at h
  rw [G.sum_map_one_add,p.selected_length] at h
  change R (p.keep.before U)=(p.selected.map rf).sum+p.arity+(if 2≤p.arity then 1 else 0)
  omega

theorem repair_rankFirst : (repairFirst p f g).rho .right (p.keep.before U)=
    1+(p.selected.map (fun a => f.rho .right a)).sum+(if 2≤p.arity then 1 else 0) := by
  have h:=G.rho_disjL_f_right (p.performR _ f) g p.keep
  have hc:=congrArg (fun n => 1+n) (p.performR_rank _ f)
  change (repairFirst p f g).rho .right (p.keep.before U)=_ at h
  omega

theorem endpoint_ltFirst (hn : 2≤p.arity) :
    (repairFirst p f g).rho .right (p.keep.before U)<(oldFirst p f g).rho .right (p.keep.before U) := by
  rw [repair_rankFirst,old_rankFirst]; omega

theorem reducesFirst {Φ Ξ Ω Ψ : List (NormalForm P)} (hn : 2≤p.arity)
    (root : G P Φ (C::Ξ)) (cutRight : G P (C::Ω) Ψ) :
    ReducesR root cutRight (oldFirst p f g) (p.keep.before U) := by
  intro a hr
  refine ⟨repairFirst p f g,?_,denoteFirst p f g,?_⟩
  · have hc:=hr.cutFree
    change (oldFirst p f g).cutCount=0 at hc
    rw [old_countFirst] at hc
    change (repairFirst p f g).cutCount=0
    rw [repair_countFirst]; exact hc
  · intro I J v b y hv
    exact ReducibilityBoundary.strict_right a _ hr (endpoint_ltFirst p f g hn) b y hv
end First
section Second
variable (q : ContractionSelection C U L) (f : G P (A::Γ) F) (g : G P (B::Θ) U)
def oldSecond : G P (.disj A B::(Γ++Θ)) (F++L) := (q.prependFixed F).performR _ (G.disjL f g)
def repairSecond : G P (.disj A B::(Γ++Θ)) (F++L) := G.disjL f (q.performR _ g)

theorem denoteSecond : ofTerm (repairSecond q f g).denote=ofTerm (oldSecond q f g).denote := by
  have hi : ofTerm (Route.identity F).coproduct=id (succ F) := Route.identity_side .disj F
  have hm : ofTerm (repairSecond q f g).denote=
      ofTerm (Rules.disjLeft (.comp f.denote (Route.identity F).coproduct) (.comp g.denote q.route.coproduct)) :=
    Rules.disjLeft_congr (by rw [ofTerm_comp,hi,Laws.comp_id]) (q.performR_denote _ g)
  have ho : ofTerm (oldSecond q f g).denote=
      comp (ofTerm (G.disjL f g).denote) (ofTerm ((Route.identity F).parallel q.route).coproduct) := by
    rw [oldSecond,ContractionSelection.performR_denote,q.prepend_route]
  exact hm.trans ((Route.parallel_disjLeft (Route.identity F) q.route f.denote g.denote).symm.trans ho.symm)

theorem old_countSecond : (oldSecond q f g).cutCount=f.cutCount+g.cutCount := by
  rw [oldSecond,ContractionSelection.performR_count]; rfl
theorem repair_countSecond : (repairSecond q f g).cutCount=f.cutCount+g.cutCount := by
  simp only [repairSecond,G.cutCount,ContractionSelection.performR_count]

theorem old_rankSecond : (oldSecond q f g).rho .right (At.shift F q.keep)=
    (q.selected.map (fun a => g.rho .right a)).sum+q.arity+(if 2≤q.arity then 1 else 0) := by
  let R : At (F++L) C→Nat := fun a => (oldSecond q f g).rho .right a
  let r : At (F++U) C→Nat := fun a => (G.disjL f g).rho .right a
  have h:=(q.prependFixed F).performR_rank _ (G.disjL f g)
  change R (q.prependFixed F).keep=((q.prependFixed F).selected.map r).sum+
    (if 2≤(q.prependFixed F).arity then 1 else 0) at h
  rw [q.prepend_keep,q.prepend_selected,q.prepend_arity] at h
  simp only [List.map_map,Function.comp_def] at h
  change (oldSecond q f g).rho .right (At.shift F q.keep)=
    (q.selected.map (fun a => (G.disjL f g).rho .right (At.shift F a))).sum+(if 2≤q.arity then 1 else 0) at h
  simp only [G.rho_disjL_g_right] at h
  let rg : At U C→Nat := fun a => g.rho .right a
  change R (At.shift F q.keep)=(q.selected.map (fun a => 1+rg a)).sum+(if 2≤q.arity then 1 else 0) at h
  rw [G.sum_map_one_add,q.selected_length] at h
  change R (At.shift F q.keep)=(q.selected.map rg).sum+q.arity+(if 2≤q.arity then 1 else 0)
  omega

theorem repair_rankSecond : (repairSecond q f g).rho .right (At.shift F q.keep)=
    1+(q.selected.map (fun a => g.rho .right a)).sum+(if 2≤q.arity then 1 else 0) := by
  have h:=G.rho_disjL_g_right f (q.performR _ g) q.keep
  have hc:=congrArg (fun n => 1+n) (q.performR_rank _ g)
  change (repairSecond q f g).rho .right (At.shift F q.keep)=_ at h
  omega

theorem endpoint_ltSecond (hn : 2≤q.arity) :
    (repairSecond q f g).rho .right (At.shift F q.keep)<(oldSecond q f g).rho .right (At.shift F q.keep) := by
  rw [repair_rankSecond,old_rankSecond]; omega

theorem reducesSecond {Φ Ξ Ω Ψ : List (NormalForm P)} (hn : 2≤q.arity)
    (root : G P Φ (C::Ξ)) (cutRight : G P (C::Ω) Ψ) :
    ReducesR root cutRight (oldSecond q f g) (At.shift F q.keep) := by
  intro a hr
  refine ⟨repairSecond q f g,?_,denoteSecond q f g,?_⟩
  · have hc:=hr.cutFree
    change (oldSecond q f g).cutCount=0 at hc
    rw [old_countSecond] at hc
    change (repairSecond q f g).cutCount=0
    rw [repair_countSecond]; exact hc
  · intro I J v b y hv
    exact ReducibilityBoundary.strict_right a _ hr (endpoint_ltSecond q f g hn) b y hv
end Second
end DosenPetric.Reduced.Gentzen.W5.OneDisjunctionSuccedent
