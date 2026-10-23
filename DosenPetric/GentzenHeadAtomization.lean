module

public import DosenPetric.GentzenRuleCongruence

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.G
universe u
variable {P : Type u}

/-- Insert a formula on the left using atomic thinnings only, without new cuts. -/
def headThinL : (A : NormalForm P) → {Γ Δ : List (NormalForm P)} → G P Γ Δ → G P (A :: Γ) Δ
  | .lit l, Γ, Δ, f => .thinL [] Γ Δ (.lit l) f
  | .top, Γ, Δ, f => .thinL [] Γ Δ .top f
  | .bot, Γ, Δ, f => .thinL [] Γ Δ .bot f
  | .conj A B, Γ, Δ, f => .conjL [] Γ Δ A B (headThinL A (headThinL B f))
  | .disj A B, Γ, Δ, f => (Rewire.dupContext Δ).right
      ((Rewire.dupTail (.disj A B) Γ).left (.disjL (headThinL A f) (headThinL B f)))

/-- Insert a formula on the right using atomic thinnings only, without new cuts. -/
def headThinR : (A : NormalForm P) → {Γ Δ : List (NormalForm P)} → G P Γ Δ → G P Γ (A :: Δ)
  | .lit l, Γ, Δ, f => .thinR Γ [] Δ (.lit l) f
  | .top, Γ, Δ, f => .thinR Γ [] Δ .top f
  | .bot, Γ, Δ, f => .thinR Γ [] Δ .bot f
  | .disj A B, Γ, Δ, f => .disjR Γ [] Δ A B (headThinR A (headThinR B f))
  | .conj A B, Γ, Δ, f => (Rewire.dupTail (.conj A B) Δ).right
      ((Rewire.dupContext Γ).left (.conjR (headThinR A f) (headThinR B f)))

theorem headThinL_atomized (A : NormalForm P) {Γ Δ : List (NormalForm P)}
    (f : G P Γ Δ) (hf : f.Atomized) : (headThinL A f).Atomized := by
  induction A generalizing Γ Δ with
  | lit => exact ⟨True.intro, hf⟩
  | top => exact ⟨True.intro, hf⟩
  | bot => exact ⟨True.intro, hf⟩
  | conj A B ih ih' => exact ih _ (ih' f hf)
  | disj A B ih ih' =>
    apply (Rewire.right_atomized _ _).mpr
    apply (Rewire.left_atomized _ _).mpr
    exact ⟨ih f hf, ih' f hf⟩

theorem headThinR_atomized (A : NormalForm P) {Γ Δ : List (NormalForm P)}
    (f : G P Γ Δ) (hf : f.Atomized) : (headThinR A f).Atomized := by
  induction A generalizing Γ Δ with
  | lit => exact ⟨True.intro, hf⟩
  | top => exact ⟨True.intro, hf⟩
  | bot => exact ⟨True.intro, hf⟩
  | disj A B ih ih' => exact ih _ (ih' f hf)
  | conj A B ih ih' =>
    apply (Rewire.right_atomized _ _).mpr
    apply (Rewire.left_atomized _ _).mpr
    exact ⟨ih f hf, ih' f hf⟩

theorem headThinL_cutFree (A : NormalForm P) {Γ Δ : List (NormalForm P)}
    (f : G P Γ Δ) (hf : f.CutFree) : (headThinL A f).CutFree := by
  induction A generalizing Γ Δ with
  | lit => exact hf
  | top => exact hf
  | bot => exact hf
  | conj A B ih ih' => exact ih _ (ih' f hf)
  | disj A B ih ih' =>
    change ((Rewire.dupContext Δ).right ((Rewire.dupTail (.disj A B) Γ).left
      (.disjL (headThinL A f) (headThinL B f)))).cutCount = 0
    rw [Rewire.right_count, Rewire.left_count]
    exact (disjL_cutFree _ _).mpr ⟨ih f hf, ih' f hf⟩

theorem headThinR_cutFree (A : NormalForm P) {Γ Δ : List (NormalForm P)}
    (f : G P Γ Δ) (hf : f.CutFree) : (headThinR A f).CutFree := by
  induction A generalizing Γ Δ with
  | lit => exact hf
  | top => exact hf
  | bot => exact hf
  | disj A B ih ih' => exact ih _ (ih' f hf)
  | conj A B ih ih' =>
    change ((Rewire.dupTail (.conj A B) Δ).right ((Rewire.dupContext Γ).left
      (.conjR (headThinR A f) (headThinR B f)))).cutCount = 0
    rw [Rewire.right_count, Rewire.left_count]
    exact (conjR_cutFree _ _).mpr ⟨ih f hf, ih' f hf⟩

theorem headThinL_denote (A : NormalForm P) {Γ Δ : List (NormalForm P)} (f : G P Γ Δ) :
    ofTerm (headThinL A f).denote = comp (snd A (ante Γ)) (ofTerm f.denote) := by
  induction A generalizing Γ Δ with
  | lit l =>
    rw [headThinL, denote_thinL]
    have h : ofTerm (Route.thin [] Γ (.lit l)).product = snd (.lit l) (ante Γ) := thin_head .conj _ _
    rw [h]
  | top =>
    rw [headThinL, denote_thinL]
    have h : ofTerm (Route.thin [] Γ .top).product = snd .top (ante Γ) := thin_head .conj _ _
    rw [h]
  | bot =>
    rw [headThinL, denote_thinL]
    have h : ofTerm (Route.thin [] Γ .bot).product = snd .bot (ante Γ) := thin_head .conj _ _
    rw [h]
  | conj A B ih ih' =>
    rw [headThinL, denote_conjL, conjLeft_head, ih, ih']
    have h := congrArg (fun k => comp k (ofTerm f.denote)) (conj_thin_head A B (ante Γ))
    simpa only [Laws.assoc] using h
  | disj A B ih ih' =>
    rw [headThinL, Rewire.right_denote, Rewire.left_denote]
    change comp (comp ((Rewire.dupTail (.disj A B) Γ).arrow .conj)
      (ofTerm (Rules.disjLeft (headThinL A f).denote (headThinL B f).denote)))
      ((Rewire.dupContext Δ).arrow .disj) = _
    have he := Rules.disjLeft_congr (f' := .comp (.snd A (ante Γ)) f.denote)
      (g' := .comp (.snd B (ante Γ)) f.denote) (ih f) (ih' f)
    rw [he]
    exact (Laws.assoc ..).trans (branchL_denote Γ Δ A B f.denote)

theorem headThinR_denote (A : NormalForm P) {Γ Δ : List (NormalForm P)} (f : G P Γ Δ) :
    ofTerm (headThinR A f).denote = comp (ofTerm f.denote) (inr A (succ Δ)) := by
  induction A generalizing Γ Δ with
  | lit l =>
    rw [headThinR, denote_thinR]
    have h : ofTerm (Route.thin [] Δ (.lit l)).coproduct = inr (.lit l) (succ Δ) := thin_head .disj _ _
    rw [h]
  | top =>
    rw [headThinR, denote_thinR]
    have h : ofTerm (Route.thin [] Δ .top).coproduct = inr .top (succ Δ) := thin_head .disj _ _
    rw [h]
  | bot =>
    rw [headThinR, denote_thinR]
    have h : ofTerm (Route.thin [] Δ .bot).coproduct = inr .bot (succ Δ) := thin_head .disj _ _
    rw [h]
  | disj A B ih ih' =>
    change comp (ofTerm (headThinR A (headThinR B f)).denote) (ofTerm (Rules.disjRight [] Δ A B).toTerm) = _
    rw [disjRight_head, ih, ih']
    simp only [Laws.assoc]
    rw [disj_thin_head]
  | conj A B ih ih' =>
    rw [headThinR, Rewire.right_denote, Rewire.left_denote]
    change comp (comp ((Rewire.dupContext Γ).arrow .conj)
      (ofTerm (Rules.conjRight (headThinR A f).denote (headThinR B f).denote)))
      ((Rewire.dupTail (.conj A B) Δ).arrow .disj) = _
    have he := Rules.conjRight_congr (f' := .comp f.denote (.inr A (succ Δ)))
      (g' := .comp f.denote (.inr B (succ Δ))) (ih f) (ih' f)
    rw [he]
    exact (Laws.assoc ..).trans (branchR_denote Γ Δ A B f.denote)

end DosenPetric.Reduced.Gentzen.G
