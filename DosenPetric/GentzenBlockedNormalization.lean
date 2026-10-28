module

public import DosenPetric.GentzenRankReplacement
public import DosenPetric.GentzenUnblockedAncestor

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u} {Γ Δ Θ Λ : List (NormalForm P)} {C : NormalForm P}

/-- Every tied left contraction in this right cut-premise has a blocked shape. -/
def AllBlockedL (g : G P (C::Θ) Λ) : Prop :=
  ∀ {U V : List (NormalForm P)} {w : G P U V}
    (a : ProofAddress g w) (x : At U C), g.TiedRight (a.traceAt .left x) → BlockedL w

/-- Every tied right contraction in this left cut-premise has a blocked shape. -/
def AllBlockedR (f : G P Γ (C::Δ)) : Prop :=
  ∀ {U V : List (NormalForm P)} {w : G P U V}
    (a : ProofAddress f w) (x : At V C), f.TiedLeft (a.traceAt .right x) → BlockedR w

/-- Normalize the tied left contractions using the full finite rank multiset. -/
theorem blocked_normalization_left (f : G P Γ (C::Δ)) (g : G P (C::Θ) Λ)
    (ht : G.Topmost f g) :
    ∃ g' : G P (C::Θ) Λ, g'.CutFree ∧ ofTerm g'.denote = ofTerm g.denote ∧ AllBlockedL g' := by
  classical
  have hwf : WellFounded (fun (new old : G P (C::Θ) Λ) =>
      FiniteRank.Descent (EligibleSites.leftRanks f new) (EligibleSites.leftRanks f old)) :=
    InvImage.wf (EligibleSites.leftRanks f) FiniteRank.descent_wf
  suffices hh : ∀ g : G P (C::Θ) Λ, G.Topmost f g →
      ∃ g' : G P (C::Θ) Λ, g'.CutFree ∧ ofTerm g'.denote = ofTerm g.denote ∧ AllBlockedL g' from hh g ht
  intro g
  induction g using hwf.induction with
  | h g ih =>
    intro ht
    by_cases hs : ∃ (o : ProofOccurrence g) (x : At o.source C), ReducibleL f g o.address x
    · obtain ⟨o,x,hr⟩ := hs
      obtain ⟨h,hcf,he,O,I,hold,hnew,hi⟩ := hr.rank_replacement
      have ht' : G.Topmost f (o.address.replace h) :=
        ⟨ht.1,o.address.replace_cutFree h ht.2 hcf⟩
      obtain ⟨g',hg',he',hb'⟩ := ih (o.address.replace h)
        (FiniteRank.of_replacement hold hnew hi) ht'
      exact ⟨g',hg',he'.trans (o.address.replace_denote h he),hb'⟩
    · refine ⟨g,ht.2,rfl,?_⟩
      intro U V w a x hx
      exact blocked_left_of_no_reducible ht
        (fun b y hy => hs ⟨ProofOccurrence.ofAddress b,y,hy⟩) a x hx

/-- The independently typed normalization of tied right contractions. -/
theorem blocked_normalization_right (f : G P Γ (C::Δ)) (g : G P (C::Θ) Λ)
    (ht : G.Topmost f g) :
    ∃ f' : G P Γ (C::Δ), f'.CutFree ∧ ofTerm f'.denote = ofTerm f.denote ∧ AllBlockedR f' := by
  classical
  have hwf : WellFounded (fun (new old : G P Γ (C::Δ)) =>
      FiniteRank.Descent (EligibleSites.rightRanks new g) (EligibleSites.rightRanks old g)) :=
    InvImage.wf (fun k => EligibleSites.rightRanks k g) FiniteRank.descent_wf
  suffices hh : ∀ f : G P Γ (C::Δ), G.Topmost f g →
      ∃ f' : G P Γ (C::Δ), f'.CutFree ∧ ofTerm f'.denote = ofTerm f.denote ∧ AllBlockedR f' from hh f ht
  intro f
  induction f using hwf.induction with
  | h f ih =>
    intro ht
    by_cases hs : ∃ (o : ProofOccurrence f) (x : At o.target C), ReducibleR f g o.address x
    · obtain ⟨o,x,hr⟩ := hs
      obtain ⟨h,hcf,he,O,I,hold,hnew,hi⟩ := hr.rank_replacement
      have ht' : G.Topmost (o.address.replace h) g :=
        ⟨o.address.replace_cutFree h ht.1 hcf,ht.2⟩
      obtain ⟨f',hf',he',hb'⟩ := ih (o.address.replace h)
        (FiniteRank.of_replacement hold hnew hi) ht'
      exact ⟨f',hf',he'.trans (o.address.replace_denote h he),hb'⟩
    · refine ⟨f,ht.1,rfl,?_⟩
      intro U V w a x hx
      exact blocked_right_of_no_reducible ht
        (fun b y hy => hs ⟨ProofOccurrence.ofAddress b,y,hy⟩) a x hx

/-- Both premises can be normalized successively. Each tied/blocked clause
depends only on its own premise and the fixed cut-entry position. -/
theorem blocked_w_premises (f : G P Γ (C::Δ)) (g : G P (C::Θ) Λ)
    (ht : G.Topmost f g) :
    ∃ (f' : G P Γ (C::Δ)) (g' : G P (C::Θ) Λ),
      G.Topmost f' g' ∧ ofTerm f'.denote = ofTerm f.denote ∧
      ofTerm g'.denote = ofTerm g.denote ∧ AllBlockedR f' ∧ AllBlockedL g' := by
  obtain ⟨f',hf',heF,hbF⟩ := blocked_normalization_right f g ht
  obtain ⟨g',hg',heG,hbG⟩ := blocked_normalization_left f' g ⟨hf',ht.2⟩
  exact ⟨f',g',⟨hf',hg'⟩,heF,heG,hbF,hbG⟩

/-- The Blocked-w Lemma at the unchanged cut formula and contexts. -/
theorem blocked_w (f : G P Γ (C::Δ)) (g : G P (C::Θ) Λ)
    (ht : G.Topmost f g) :
    ∃ (f' : G P Γ (C::Δ)) (g' : G P (C::Θ) Λ),
      G.Topmost f' g' ∧ ofTerm (G.cut f' g').denote = ofTerm (G.cut f g).denote ∧
      (∀ {U V : List (NormalForm P)} {w : G P U V}
        (a : ProofAddress g' w) (x : At U C),
        g'.TiedRight (a.traceAt .left x) → BlockedL w) ∧
      (∀ {U V : List (NormalForm P)} {w : G P U V}
        (a : ProofAddress f' w) (x : At V C),
        f'.TiedLeft (a.traceAt .right x) → BlockedR w) := by
  obtain ⟨f',g',ht',heF,heG,hbF,hbG⟩ := blocked_w_premises f g ht
  exact ⟨f',g',ht',Rules.cut_congr heF heG,hbG,hbF⟩

end DosenPetric.Reduced.Gentzen
