module

public import DosenPetric.GentzenDispatchRules
public import DosenPetric.GentzenReducibleOccurrences
public import DosenPetric.GentzenSingleMixExamples

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.BlockedExamples
universe u
variable {P : Type u}
open BlockedSource W5.SinglePremiseMix.Examples

def l (Γ : List (NormalForm Empty)) := G.atomize (W1.SameSideLogical.constantLeft Γ)
def r (Δ : List (NormalForm Empty)) := G.atomize (W1.SameSideLogical.constantRight Δ)

theorem left_gamma_mix : ∃ g : G Empty [.top] [.top,.top], BlockedL g :=
  ⟨_,.gammaMix .top [] [] [] [] [.top] [.top] (l [.top]) (l [.top])⟩
theorem left_gamma_conj : ∃ g : G Empty [.top] [.conj .top .top], BlockedL g :=
  ⟨_,.gammaConj .top .top .top [] [] [] [] [] [] (l [.top]) (l [.top])⟩
theorem left_gamma_disj : ∃ g : G Empty [.top,.disj .top .bot] [.top,.top], BlockedL g :=
  ⟨_,.gammaDisj .top .top .bot [] [] [] [] [.top] [.top] (l [.top,.top]) (l [.top,.bot])⟩
theorem left_conjunction : ∃ g : G Empty [.conj .top .bot] [.top], BlockedL g :=
  ⟨_,.conjunction .top .bot [] [] [.top] (l [.conj .top .bot,.top,.bot])⟩
theorem left_disj_first : ∃ g : G Empty [.disj .top .bot] [.top,.top], BlockedL g :=
  ⟨_,.disjunctionFirst .top .bot [] [] [] [.top] [.top] (l [.disj .top .bot,.top]) (l [.bot])⟩
theorem left_disj_second : ∃ g : G Empty [.disj .top .bot] [.top,.top], BlockedL g :=
  ⟨_,.disjunctionSecond .top .bot [] [] [] [.top] [.top] (l [.top]) (l [.disj .top .bot,.bot])⟩
theorem left_disj_both : ∃ g : G Empty [.disj .top .bot] [.top,.top], BlockedL g :=
  ⟨_,.disjunctionBoth .top .bot [] [] [] [] [.top] [.top]
    (l [.disj .top .bot,.top]) (l [.disj .top .bot,.bot])⟩

theorem right_gamma_mix : ∃ g : G Empty [.bot,.bot] [.top], BlockedR g :=
  ⟨_,.gammaMix .top [.bot] [.bot] [] [] [] [] (r [.top]) (r [.top])⟩
theorem right_gamma_disj : ∃ g : G Empty [.disj .bot .bot] [.top], BlockedR g :=
  ⟨_,.gammaDisj .top .bot .bot [] [] [] [] [] [] (r [.top]) (r [.top])⟩
theorem right_gamma_conj : ∃ g : G Empty [.bot,.bot] [.conj .bot .bot,.top], BlockedR g :=
  ⟨_,.gammaConj .top .bot .bot [.bot] [.bot] [] [] [] [] (r [.bot,.top]) (r [.bot,.top])⟩
theorem right_disjunction : ∃ g : G Empty [.bot] [.disj .bot .bot], BlockedR g :=
  ⟨_,.disjunction .bot .bot [.bot] [] [] (r [.bot,.bot,.disj .bot .bot])⟩
theorem right_conj_first : ∃ g : G Empty [.bot,.bot] [.conj .bot .bot], BlockedR g :=
  ⟨_,.conjunctionFirst .bot .bot [.bot] [.bot] [] [] [] (r [.bot,.conj .bot .bot]) (r [.bot])⟩
theorem right_conj_second : ∃ g : G Empty [.bot,.bot] [.conj .bot .bot], BlockedR g :=
  ⟨_,.conjunctionSecond .bot .bot [.bot] [.bot] [] [] [] (r [.bot]) (r [.bot,.conj .bot .bot])⟩
theorem right_conj_both : ∃ g : G Empty [.bot,.bot] [.conj .bot .bot], BlockedR g :=
  ⟨_,.conjunctionBoth .bot .bot [.bot] [.bot] [] [] [] []
    (r [.bot,.conj .bot .bot]) (r [.bot,.conj .bot .bot])⟩

def splitMix (t : Literal P) := G.mix (G.identity t) (G.identity t)
theorem splitMix_ports (t : Literal P) :
    (splitMix t).selectionPorts .left (two (.lit t)).selected = [.second,.first] := by
  change [(splitMix t).selectionPort .left (.here (.lit t) [.lit t]),
    (splitMix t).selectionPort .left (.there (.here (.lit t) []))] = _
  have h₀ := G.selectionPort_eq (splitMix t) .left (.here _ _) .second (PortOrigin.second
    ⟨⟨_,_,G.identity t,Premise.mix_right _ _⟩,.here (.lit t) []⟩ rfl rfl)
  have h₁ := G.selectionPort_eq (splitMix t) .left (.there (.here _ _)) .first (PortOrigin.first
    ⟨⟨_,_,G.identity t,Premise.mix_left _ _⟩,.here (.lit t) []⟩ rfl rfl)
  exact congr (congrArg List.cons h₀) (congrArg (fun p => [p]) h₁)

theorem splitMix_regime (t : Literal P) :
    SelectionRegime.parametricBoth.Holds ((splitMix t).selectionPorts .left (two (.lit t)).selected) := by
  rw [splitMix_ports]
  unfold SelectionRegime.Holds
  decide

def freshBoth : G Empty [.disj .top .bot,.disj .top .bot,.disj .top .bot] [.top,.top] :=
  G.disjL (l [.top,.disj .top .bot]) (l [.bot,.disj .top .bot])
theorem freshBoth_ports : freshBoth.selectionPorts .left (three (.disj .top .bot)).selected =
    [.fresh,.first,.second] := by
  change [freshBoth.selectionPort .left (.here _ _),
    freshBoth.selectionPort .left (.there (.here _ _)),
    freshBoth.selectionPort .left (.there (.there (.here _ _)))] = _
  rw [G.selectionPort_eq freshBoth .left (.here _ _) .fresh (.fresh rfl),
    G.selectionPort_eq freshBoth .left (.there (.here _ _)) .first (.first
      ⟨⟨_,_,l [.top,.disj .top .bot],Premise.disjL_left _ _⟩,.there (.here _ _)⟩ rfl rfl),
    G.selectionPort_eq freshBoth .left (.there (.there (.here _ _))) .second (.second
      ⟨⟨_,_,l [.bot,.disj .top .bot],Premise.disjL_right _ _⟩,.there (.here _ _)⟩ rfl rfl)]

theorem freshBoth_regime : SelectionRegime.selectedBoth.Holds
    (freshBoth.selectionPorts .left (three (.disj .top .bot)).selected) := by
  rw [freshBoth_ports]
  unfold SelectionRegime.Holds
  decide

def freshFirst : G Empty [.disj .top .bot,.disj .top .bot] [.top,.top] :=
  G.disjL (l [.top,.disj .top .bot]) (l [.bot])
theorem freshFirst_ports : freshFirst.selectionPorts .left (two (.disj .top .bot)).selected =
    [.fresh,.first] := by
  change [freshFirst.selectionPort .left (.here _ _),freshFirst.selectionPort .left (.there (.here _ _))] = _
  rw [G.selectionPort_eq freshFirst .left (.here _ _) .fresh (.fresh rfl),G.selectionPort_eq freshFirst .left (.there (.here _ _)) .first (.first
    ⟨⟨_,_,l [.top,.disj .top .bot],Premise.disjL_left _ _⟩,.there (.here _ _)⟩ rfl rfl)]

def freshSecond : G Empty [.disj .top .bot,.disj .top .bot] [.top,.top] :=
  G.disjL (l [.top]) (l [.bot,.disj .top .bot])
theorem freshSecond_ports : freshSecond.selectionPorts .left (two (.disj .top .bot)).selected =
    [.fresh,.second] := by
  change [freshSecond.selectionPort .left (.here _ _),freshSecond.selectionPort .left (.there (.here _ _))] = _
  rw [G.selectionPort_eq freshSecond .left (.here _ _) .fresh (.fresh rfl),G.selectionPort_eq freshSecond .left (.there (.here _ _)) .second (.second
    ⟨⟨_,_,l [.bot,.disj .top .bot],Premise.disjL_right _ _⟩,.there (.here _ _)⟩ rfl rfl)]

theorem fresh_single_branch_regimes :
    SelectionRegime.selectedFirst.Holds (freshFirst.selectionPorts .left (two (.disj .top .bot)).selected) ∧
    SelectionRegime.selectedSecond.Holds (freshSecond.selectionPorts .left (two (.disj .top .bot)).selected) := by
  rw [freshFirst_ports,freshSecond_ports]
  unfold SelectionRegime.Holds
  decide

def shared (t : Literal P) : G P [.lit t,.lit t] [.lit t] :=
  G.contractL (.lit t) [[],[]] [.lit t] [.lit t] (Nat.le_refl 2)
    (W4.SelectedLogical.Examples.prefixL [.lit t,.lit t] (G.identity t))
theorem shared_regime (t : Literal P) :
    SelectionRegime.shared.Holds ((shared t).selectionPorts .left (two (.lit t)).selected) := by
  apply (shared t).port_member .left (two (.lit t)).selected .shared |>.mpr
  exact ⟨.here _ _,List.mem_cons_self,.shared (.left ..)⟩

theorem same_label_fixed_principal (t : Literal P) :
    (shared t).selectionPort .left (.there (.here (.lit t) [])) = .first :=
  G.selectionPort_eq (shared t) .left (.there (.here _ _)) .first (.first
    ⟨⟨_,_,_,Premise.contractL (.lit t) [[],[]] [.lit t] [.lit t] (Nat.le_refl 2) _⟩,
      .there (.there (.here _ _))⟩ rfl rfl)

def unaryFixed : G Empty [.top,.top,.top] [.top] :=
  G.thinL [] [.top,.top] [.top] .top (l [.top,.top])
theorem unaryFixed_ports : unaryFixed.selectionPorts .left
    (W5.SinglePremiseMix.block .top [[.top],[]] []).selected = [.first,.first] := by
  change [unaryFixed.selectionPort .left (.there (.here _ _)),
    unaryFixed.selectionPort .left (.there (.there (.here _ _)))] = _
  have h₀ := G.selectionPort_eq unaryFixed .left (.there (.here _ _)) .first (.first
    ⟨⟨_,_,l [.top,.top],Premise.thinL [] [.top,.top] [.top] .top _⟩,.here _ _⟩ rfl rfl)
  have h₁ := G.selectionPort_eq unaryFixed .left (.there (.there (.here _ _))) .first (.first
    ⟨⟨_,_,l [.top,.top],Premise.thinL [] [.top,.top] [.top] .top _⟩,.there (.here _ _)⟩ rfl rfl)
  exact congr (congrArg List.cons h₀) (congrArg (fun p => [p]) h₁)

def onlySecond : G Empty [.top,.top] [.top,.top] := G.mix G.topI (l [.top,.top])
theorem onlySecond_ports : onlySecond.selectionPorts .left (two .top).selected = [.second,.second] := by
  change [onlySecond.selectionPort .left (.here _ _),onlySecond.selectionPort .left (.there (.here _ _))] = _
  have h₀ := G.selectionPort_eq onlySecond .left (.here _ _) .second (.second
    ⟨⟨_,_,l [.top,.top],Premise.mix_right G.topI _⟩,.here _ _⟩ rfl rfl)
  have h₁ := G.selectionPort_eq onlySecond .left (.there (.here _ _)) .second (.second
    ⟨⟨_,_,l [.top,.top],Premise.mix_right G.topI _⟩,.there (.here _ _)⟩ rfl rfl)
  exact congr (congrArg List.cons h₀) (congrArg (fun p => [p]) h₁)

theorem single_branch_parametric_regimes :
    SelectionRegime.parametricFirst.Holds (unaryFixed.selectionPorts .left
      (W5.SinglePremiseMix.block .top [[.top],[]] []).selected) ∧
    SelectionRegime.parametricSecond.Holds (onlySecond.selectionPorts .left (two .top).selected) := by
  rw [unaryFixed_ports,onlySecond_ports]
  unfold SelectionRegime.Holds
  decide

theorem three_selected_principal_indices :
    (selectedCopies (.disj (.top : NormalForm Empty) .bot) [[],[],[]] []).map At.index = [0,1,2] :=
  (selectedCopies_indices ..).trans rfl

def sourceRightNonempty : G Empty [.bot] [.top,.top,.bot] :=
  sourceRight2 .top [.bot] [.top] [.bot] [] (r [.top,.top,.bot,.top])

theorem sourceRightNonempty_count : sourceRightNonempty.cutCount = (r [.top,.top,.bot,.top]).cutCount :=
  sourceRight2_count ..

theorem sibling_ancestry {Γ Δ : List (NormalForm P)} (f : G P Γ Δ) :
    ¬ (ProofAddress.root.down (Premise.mix_left f f)).ProperContains
      (ProofAddress.root.down (Premise.mix_right f f)) := by
  intro h
  have he := ProofAddress.proper_length h
  change 1 < 1 at he
  omega

theorem proper_nested (t : Literal P) :
    (ProofAddress.root : ProofAddress (G.mix (shared t) (shared t)) (G.mix (shared t) (shared t))).ProperContains
      (ProofAddress.root.down (Premise.mix_left (shared t) (shared t))) := ProofAddress.down_proper ..

end DosenPetric.Reduced.Gentzen.BlockedExamples
