module

public import DosenPetric.GentzenPositionalThinning

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.G
universe u
variable {P : Type u}

/-- Atomize the original premises first, then replace each positional thinning. -/
def atomize : {Γ Δ : List (NormalForm P)} → G P Γ Δ → G P Γ Δ
  | _, _, .identity l => .identity l
  | _, _, .zero l => .zero l
  | _, _, .topI => .topI
  | _, _, .botE => .botE
  | _, _, .exchangeL Γ X Y Θ Δ f => .exchangeL Γ X Y Θ Δ (atomize f)
  | _, _, .exchangeR Γ Δ X Y Λ f => .exchangeR Γ Δ X Y Λ (atomize f)
  | _, _, .thinL Γ Θ Δ A f => atomThinL Γ Θ Δ A (atomize f)
  | _, _, .thinR Γ Δ Λ A f => atomThinR Γ Δ Λ A (atomize f)
  | _, _, .contractL C gs Θ Δ hn f => .contractL C gs Θ Δ hn (atomize f)
  | _, _, .contractR Γ C gs Λ hn f => .contractR Γ C gs Λ hn (atomize f)
  | _, _, .conjL Γ Θ Δ A B f => .conjL Γ Θ Δ A B (atomize f)
  | _, _, .disjR Γ Δ Λ A B f => .disjR Γ Δ Λ A B (atomize f)
  | _, _, .conjR f g => .conjR (atomize f) (atomize g)
  | _, _, .disjL f g => .disjL (atomize f) (atomize g)
  | _, _, .mix f g => .mix (atomize f) (atomize g)
  | _, _, .cut f g => .cut (atomize f) (atomize g)

theorem atomize_atomized {Γ Δ : List (NormalForm P)} (g : G P Γ Δ) : (atomize g).Atomized := by
  induction g with
  | identity => trivial
  | zero => trivial
  | topI => trivial
  | botE => trivial
  | exchangeL _ _ _ _ _ _ ih => exact ih
  | exchangeR _ _ _ _ _ _ ih => exact ih
  | thinL Γ Θ Δ A f ih => exact atomThinL_atomized Γ Θ Δ A _ ih
  | thinR Γ Δ Λ A f ih => exact atomThinR_atomized Γ Δ Λ A _ ih
  | contractL _ _ _ _ _ _ ih => exact ih
  | contractR _ _ _ _ _ _ ih => exact ih
  | conjL _ _ _ _ _ _ ih => exact ih
  | disjR _ _ _ _ _ _ ih => exact ih
  | conjR _ _ ih ih' => exact ⟨ih, ih'⟩
  | disjL _ _ ih ih' => exact ⟨ih, ih'⟩
  | mix _ _ ih ih' => exact ⟨ih, ih'⟩
  | cut _ _ ih ih' => exact ⟨ih, ih'⟩

theorem atomize_cutFree {Γ Δ : List (NormalForm P)} (g : G P Γ Δ)
    (hg : g.CutFree) : (atomize g).CutFree := by
  induction g with
  | identity => rfl
  | zero => rfl
  | topI => rfl
  | botE => rfl
  | exchangeL _ _ _ _ _ _ ih => exact ih hg
  | exchangeR _ _ _ _ _ _ ih => exact ih hg
  | thinL Γ Θ Δ A f ih => exact atomThinL_cutFree Γ Θ Δ A _ (ih hg)
  | thinR Γ Δ Λ A f ih => exact atomThinR_cutFree Γ Δ Λ A _ (ih hg)
  | contractL _ _ _ _ _ _ ih => exact ih hg
  | contractR _ _ _ _ _ _ ih => exact ih hg
  | conjL _ _ _ _ _ _ ih => exact ih hg
  | disjR _ _ _ _ _ _ ih => exact ih hg
  | conjR f g ih ih' =>
    apply (conjR_cutFree _ _).mpr
    exact ⟨ih ((conjR_cutFree f g).mp hg).1, ih' ((conjR_cutFree f g).mp hg).2⟩
  | disjL f g ih ih' =>
    apply (disjL_cutFree _ _).mpr
    exact ⟨ih ((disjL_cutFree f g).mp hg).1, ih' ((disjL_cutFree f g).mp hg).2⟩
  | mix f g ih ih' =>
    apply (mix_cutFree _ _).mpr
    exact ⟨ih ((mix_cutFree f g).mp hg).1, ih' ((mix_cutFree f g).mp hg).2⟩
  | cut f g _ _ => exact False.elim (cut_not_cutFree f g hg)

theorem atomize_denote {Γ Δ : List (NormalForm P)} (g : G P Γ Δ) :
    ofTerm (atomize g).denote = ofTerm g.denote := by
  induction g with
  | identity => rfl
  | zero => rfl
  | topI => rfl
  | botE => rfl
  | exchangeL Γ X Y Θ Δ f ih =>
    simp only [atomize, denote, ofTerm_comp]; rw [ih]
  | exchangeR Γ Δ X Y Λ f ih =>
    simp only [atomize, denote, ofTerm_comp]; rw [ih]
  | thinL Γ Θ Δ A f ih =>
    rw [atomize, atomThinL_denote]
    simp only [denote, ofTerm_comp]; rw [ih]
  | thinR Γ Δ Λ A f ih =>
    rw [atomize, atomThinR_denote]
    simp only [denote, ofTerm_comp]; rw [ih]
  | contractL C gs Θ Δ hn f ih =>
    simp only [atomize, denote, ofTerm_comp]; rw [ih]
  | contractR Γ C gs Λ hn f ih =>
    simp only [atomize, denote, ofTerm_comp]; rw [ih]
  | conjL Γ Θ Δ A B f ih =>
    simp only [atomize, denote, ofTerm_comp]; rw [ih]
  | disjR Γ Δ Λ A B f ih =>
    simp only [atomize, denote, ofTerm_comp]; rw [ih]
  | conjR f g ih ih' => exact Rules.conjRight_congr ih ih'
  | disjL f g ih ih' => exact Rules.disjLeft_congr ih ih'
  | mix f g ih ih' => exact Rules.mix_congr ih ih'
  | cut f g ih ih' => exact Rules.cut_congr ih ih'

/-- Atomic-k with unchanged endpoints and preservation of any existing cut-freeness. -/
theorem atomization {Γ Δ : List (NormalForm P)} (g : G P Γ Δ) :
    ∃ h : G P Γ Δ, h.Atomized ∧ (g.CutFree → h.CutFree) ∧ ofTerm h.denote = ofTerm g.denote :=
  ⟨atomize g, atomize_atomized g, atomize_cutFree g, atomize_denote g⟩

theorem atomization_cutFree {Γ Δ : List (NormalForm P)} (g : G P Γ Δ) (hg : g.CutFree) :
    ∃ h : G P Γ Δ, h.Atomized ∧ h.CutFree ∧ ofTerm h.denote = ofTerm g.denote :=
  ⟨atomize g, atomize_atomized g, atomize_cutFree g hg, atomize_denote g⟩

theorem atomize_relation {Γ Δ : List (NormalForm P)} (g : G P Γ Δ) :
    (atomize g).relation = g.relation :=
  congrArg occurrenceMap (atomize_denote g)

theorem atomization_occurrences {Γ Δ : List (NormalForm P)} (g : G P Γ Δ) :
    ∃ h : G P Γ Δ, h.Atomized ∧ (g.CutFree → h.CutFree) ∧
      ofTerm h.denote = ofTerm g.denote ∧ h.relation = g.relation :=
  ⟨atomize g, atomize_atomized g, atomize_cutFree g, atomize_denote g, atomize_relation g⟩

end DosenPetric.Reduced.Gentzen.G
