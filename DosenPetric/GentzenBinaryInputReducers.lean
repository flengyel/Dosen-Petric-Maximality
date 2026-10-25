module

public import DosenPetric.GentzenDisjunctionAntecedentReducer
public import DosenPetric.GentzenDisjunctionSuccedentReducer
public import DosenPetric.GentzenMixInputReducer
public import DosenPetric.GentzenDispatchRules

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.BinaryReducer
universe u
variable {P : Type u} {C : NormalForm P} {F K V U Φ Ξ Ω Ψ : List (NormalForm P)}

theorem selection_left (s : ContractionSelection C F K) (hn : 2≤s.arity)
    (f : G P F V) (hb : f.ruleKind.Binary)
    (cutLeft : G P Φ (C::Ξ)) (root : G P (C::Ω) Ψ) :
    ReducesL cutLeft root (s.performL _ f) s.keep := by
  intro a hr
  have hc : f.cutCount=0 := by
    have h:=hr.cutFree
    change (s.performL _ f).cutCount=0 at h
    rwa [ContractionSelection.performL_count] at h
  cases f <;> simp only [G.ruleKind,G.RuleKind.Binary] at hb
  case conjR f g => exact ConjunctionReducer.selection_left s hn f g cutLeft root a hr
  case disjL f g => exact DisjunctionReducer.selection_left s hn f g cutLeft root a hr
  case mix f g =>
    have he : ReducesL cutLeft root (s.performL _ (G.mix f g)) s.keep := by
      rw [ContractionSelection.performL_eq_apply _ hn]
      exact fun a hr => MixReducer.selection_left s hn f g a hr
    exact he a hr
  case cut => simp only [G.cutCount] at hc; omega

theorem selection_right (s : ContractionSelection C V K) (hn : 2≤s.arity)
    (f : G P U V) (hb : f.ruleKind.Binary)
    (root : G P Φ (C::Ξ)) (cutRight : G P (C::Ω) Ψ) :
    ReducesR root cutRight (s.performR _ f) s.keep := by
  intro a hr
  have hc : f.cutCount=0 := by
    have h:=hr.cutFree
    change (s.performR _ f).cutCount=0 at h
    rwa [ContractionSelection.performR_count] at h
  cases f <;> simp only [G.ruleKind,G.RuleKind.Binary] at hb
  case conjR f g => exact ConjunctionReducer.selection_right s hn f g root cutRight a hr
  case disjL f g => exact DisjunctionReducer.selection_right s hn f g root cutRight a hr
  case mix f g =>
    have he : ReducesR root cutRight (s.performR _ (G.mix f g)) s.keep := by
      rw [ContractionSelection.performR_eq_apply _ hn]
      exact fun a hr => MixReducer.selection_right s hn f g a hr
    exact he a hr
  case cut => simp only [G.cutCount] at hc; omega

/-- Every actual left contraction whose premise is a binary Gentzen rule.
The cut-premise case is excluded by reducibility's existing cut-freeness. -/
theorem left (d : ContractionBlock P F K) (hn : 2≤d.gs.length)
    (f : G P F V) (hb : f.ruleKind.Binary)
    (cutLeft : G P Φ (d.C::Ξ)) (root : G P (d.C::Ω) Ψ) :
    ReducesL cutLeft root (d.applyL hn _ f) d.keep := by
  let p:=d.selection (d.nonempty hn)
  have he : p.block=d := d.selection_block _
  have hp : 2≤p.arity := by
    have h:=congrArg (fun b=>b.gs.length) he
    change p.gs.length=d.gs.length at h
    have hc:=p.count
    omega
  have h:=selection_left p hp f hb cutLeft root
  have hw : p.performL _ f=d.applyL hn _ f :=
    (p.performL_eq_apply hp _).trans (ContractionBlock.applyL_congr he _ _ _ _)
  have hx : p.keep=d.keep := d.selection_keep hn
  rw [hw,hx] at h
  exact h

theorem right (d : ContractionBlock P V K) (hn : 2≤d.gs.length)
    (f : G P U V) (hb : f.ruleKind.Binary)
    (root : G P Φ (d.C::Ξ)) (cutRight : G P (d.C::Ω) Ψ) :
    ReducesR root cutRight (d.applyR hn _ f) d.keep := by
  let p:=d.selection (d.nonempty hn)
  have he : p.block=d := d.selection_block _
  have hp : 2≤p.arity := by
    have h:=congrArg (fun b=>b.gs.length) he
    change p.gs.length=d.gs.length at h
    have hc:=p.count
    omega
  have h:=selection_right p hp f hb root cutRight
  have hw : p.performR _ f=d.applyR hn _ f :=
    (p.performR_eq_apply hp _).trans (ContractionBlock.applyR_congr he _ _ _ _)
  have hx : p.keep=d.keep := d.selection_keep hn
  rw [hw,hx] at h
  exact h
end DosenPetric.Reduced.Gentzen.BinaryReducer
