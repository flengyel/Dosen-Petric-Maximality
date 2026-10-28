module

public import DosenPetric.GentzenChosenRankReplacement
public import DosenPetric.GentzenBlockedNormalization
public import DosenPetric.GentzenUnblockedAncestor

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u} {Γ Δ Θ Λ : List (NormalForm P)} {C : NormalForm P}

/-- Normalize the tied left contractions using the full finite rank multiset. -/
theorem blocked_normalization_left_atomized (f : G P Γ (C::Δ)) (g : G P (C::Θ) Λ)
    (ht : G.Topmost f g) (hat : g.Atomized) :
    ∃ g' : G P (C::Θ) Λ, g'.CutFree ∧ g'.Atomized ∧ ofTerm g'.denote = ofTerm g.denote ∧ AllBlockedL g' := by
  classical
  have hwf : WellFounded (fun (new old : G P (C::Θ) Λ) =>
      FiniteRank.Descent (EligibleSites.leftRanks f new) (EligibleSites.leftRanks f old)) :=
    InvImage.wf (EligibleSites.leftRanks f) FiniteRank.descent_wf
  suffices hh : ∀ g : G P (C::Θ) Λ, G.Topmost f g → g.Atomized →
      ∃ g' : G P (C::Θ) Λ, g'.CutFree ∧ g'.Atomized ∧ ofTerm g'.denote = ofTerm g.denote ∧ AllBlockedL g' from hh g ht hat
  intro g
  induction g using hwf.induction with
  | h g ih =>
    intro ht hat
    by_cases hs : ∃ (o : ProofOccurrence g) (x : At o.source C), ReducibleL f g o.address x
    · obtain ⟨o,x,hr⟩ := hs
      obtain ⟨h,hcf,ha,he,hbound⟩ := reducibility_left_atomized f g o.proof x
        (o.address.atomized hat) o.address hr
      obtain ⟨O,I,hold,hnew,hi⟩ := hr.rank_replacement_for h hcf hbound
      have ht' : G.Topmost f (o.address.replace h) :=
        ⟨ht.1,o.address.replace_cutFree h ht.2 hcf⟩
      obtain ⟨g',hg',ha',he',hb'⟩ := ih (o.address.replace h)
        (FiniteRank.of_replacement hold hnew hi) ht' (o.address.replace_atomized h hat ha)
      exact ⟨g',hg',ha',he'.trans (o.address.replace_denote h he),hb'⟩
    · refine ⟨g,ht.2,hat,rfl,?_⟩
      intro U V w a x hx
      exact blocked_left_of_no_reducible ht
        (fun b y hy => hs ⟨ProofOccurrence.ofAddress b,y,hy⟩) a x hx

/-- The independently typed normalization of tied right contractions. -/
theorem blocked_normalization_right_atomized (f : G P Γ (C::Δ)) (g : G P (C::Θ) Λ)
    (ht : G.Topmost f g) (hat : f.Atomized) :
    ∃ f' : G P Γ (C::Δ), f'.CutFree ∧ f'.Atomized ∧ ofTerm f'.denote = ofTerm f.denote ∧ AllBlockedR f' := by
  classical
  have hwf : WellFounded (fun (new old : G P Γ (C::Δ)) =>
      FiniteRank.Descent (EligibleSites.rightRanks new g) (EligibleSites.rightRanks old g)) :=
    InvImage.wf (fun k => EligibleSites.rightRanks k g) FiniteRank.descent_wf
  suffices hh : ∀ f : G P Γ (C::Δ), G.Topmost f g → f.Atomized →
      ∃ f' : G P Γ (C::Δ), f'.CutFree ∧ f'.Atomized ∧ ofTerm f'.denote = ofTerm f.denote ∧ AllBlockedR f' from hh f ht hat
  intro f
  induction f using hwf.induction with
  | h f ih =>
    intro ht hat
    by_cases hs : ∃ (o : ProofOccurrence f) (x : At o.target C), ReducibleR f g o.address x
    · obtain ⟨o,x,hr⟩ := hs
      obtain ⟨h,hcf,ha,he,hbound⟩ := reducibility_right_atomized f g o.proof x
        (o.address.atomized hat) o.address hr
      obtain ⟨O,I,hold,hnew,hi⟩ := hr.rank_replacement_for h hcf hbound
      have ht' : G.Topmost (o.address.replace h) g :=
        ⟨o.address.replace_cutFree h ht.1 hcf,ht.2⟩
      obtain ⟨f',hf',ha',he',hb'⟩ := ih (o.address.replace h)
        (FiniteRank.of_replacement hold hnew hi) ht' (o.address.replace_atomized h hat ha)
      exact ⟨f',hf',ha',he'.trans (o.address.replace_denote h he),hb'⟩
    · refine ⟨f,ht.1,hat,rfl,?_⟩
      intro U V w a x hx
      exact blocked_right_of_no_reducible ht
        (fun b y hy => hs ⟨ProofOccurrence.ofAddress b,y,hy⟩) a x hx

end DosenPetric.Reduced.Gentzen
