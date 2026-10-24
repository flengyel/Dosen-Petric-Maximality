module

public import DosenPetric.GentzenTraceCompatibility
public import DosenPetric.GentzenRuleCongruence

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.Premise
universe u
variable {P : Type u} {Γ Δ Θ Λ : List (NormalForm P)}
variable {f : G P Γ Δ} {g : G P Θ Λ}

/-- Rebuild one rule with precisely its selected premise replaced. -/
def rebuild (p : Premise f g) : G P Θ Λ → G P Γ Δ := match p with
  | .exchangeL Γ X Y Θ Δ _ => fun h => .exchangeL Γ X Y Θ Δ h
  | .exchangeR Γ Δ X Y Λ _ => fun h => .exchangeR Γ Δ X Y Λ h
  | .thinL Γ Θ Δ A _ => fun h => .thinL Γ Θ Δ A h
  | .thinR Γ Δ Λ A _ => fun h => .thinR Γ Δ Λ A h
  | .contractL C gs Θ Δ hn _ => fun h => .contractL C gs Θ Δ hn h
  | .contractR Γ C gs Λ hn _ => fun h => .contractR Γ C gs Λ hn h
  | .conjL Γ Θ Δ A B _ => fun h => .conjL Γ Θ Δ A B h
  | .disjR Γ Δ Λ A B _ => fun h => .disjR Γ Δ Λ A B h
  | .conjR_left _ k => fun h => .conjR h k
  | .conjR_right k _ => fun h => .conjR k h
  | .disjL_left _ k => fun h => .disjL h k
  | .disjL_right k _ => fun h => .disjL k h
  | .mix_left _ k => fun h => .mix h k
  | .mix_right k _ => fun h => .mix k h
  | @cut_left _ _ _ _ _ C _ k => fun h => G.cut (C := C) h k
  | @cut_right _ _ _ _ _ C k _ => fun h => G.cut (C := C) k h

theorem rebuild_original (p : Premise f g) : p.rebuild g = f := by cases p <;> rfl

/-- The inserted proof has the same immediate branch in the rebuilt rule. -/
def inserted (p : Premise f g) : (h : G P Θ Λ) → Premise (p.rebuild h) h := match p with
  | .exchangeL Γ X Y Θ Δ _ => fun h => .exchangeL Γ X Y Θ Δ h
  | .exchangeR Γ Δ X Y Λ _ => fun h => .exchangeR Γ Δ X Y Λ h
  | .thinL Γ Θ Δ A _ => fun h => .thinL Γ Θ Δ A h
  | .thinR Γ Δ Λ A _ => fun h => .thinR Γ Δ Λ A h
  | .contractL C gs Θ Δ hn _ => fun h => .contractL C gs Θ Δ hn h
  | .contractR Γ C gs Λ hn _ => fun h => .contractR Γ C gs Λ hn h
  | .conjL Γ Θ Δ A B _ => fun h => .conjL Γ Θ Δ A B h
  | .disjR Γ Δ Λ A B _ => fun h => .disjR Γ Δ Λ A B h
  | .conjR_left _ k => fun h => .conjR_left h k
  | .conjR_right k _ => fun h => .conjR_right k h
  | .disjL_left _ k => fun h => .disjL_left h k
  | .disjL_right k _ => fun h => .disjL_right k h
  | .mix_left _ k => fun h => .mix_left h k
  | .mix_right k _ => fun h => .mix_right k h
  | @cut_left _ _ _ _ _ C _ k => fun h => Premise.cut_left (C := C) h k
  | @cut_right _ _ _ _ _ C k _ => fun h => Premise.cut_right (C := C) k h

theorem inserted_branch (p : Premise f g) (h : G P Θ Λ) :
    (p.inserted h).branch = p.branch := by cases p <;> rfl

theorem rebuild_inserted (p : Premise f g) (h k : G P Θ Λ) :
    (p.inserted h).rebuild k = p.rebuild k := by cases p <;> rfl

theorem rebuild_denote (p : Premise f g) (h : G P Θ Λ)
    (he : ofTerm h.denote = ofTerm g.denote) :
    ofTerm (p.rebuild h).denote = ofTerm f.denote := by
  cases p <;> simp only [rebuild,G.denote,ofTerm_comp]
  all_goals first
    | rw [he]
    | exact Rules.conjRight_congr he rfl
    | exact Rules.conjRight_congr rfl he
    | exact Rules.disjLeft_congr he rfl
    | exact Rules.disjLeft_congr rfl he
    | exact Rules.mix_congr he rfl
    | exact Rules.mix_congr rfl he
    | exact Rules.cut_congr he rfl
    | exact Rules.cut_congr rfl he

theorem rebuild_cutCount (p : Premise f g) (h : G P Θ Λ) :
    (p.rebuild h).cutCount + g.cutCount = f.cutCount + h.cutCount := by
  cases p <;> simp only [rebuild,G.cutCount] <;> omega

theorem rebuild_proofSize (p : Premise f g) (h : G P Θ Λ) :
    (p.rebuild h).proofSize + g.proofSize = f.proofSize + h.proofSize := by
  cases p <;> simp only [rebuild,G.proofSize] <;> omega

theorem rebuild_cutFree (p : Premise f g) (h : G P Θ Λ)
    (hf : f.CutFree) (hh : h.CutFree) : (p.rebuild h).CutFree := by
  have he := p.rebuild_cutCount h
  unfold G.CutFree at *
  omega

theorem rebuild_atomized (p : Premise f g) (h : G P Θ Λ)
    (hf : f.Atomized) (hh : h.Atomized) : (p.rebuild h).Atomized := by
  cases p <;> simp only [rebuild,G.Atomized] at hf ⊢
  all_goals first | exact hh | exact ⟨hf.1,hh⟩ | exact ⟨hh,hf.2⟩

end DosenPetric.Reduced.Gentzen.Premise
