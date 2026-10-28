module

public import DosenPetric.GentzenCutEliminationSpec

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

/-- All possible whole-formula leaves on the right of an atomized proof. -/
inductive RightLeaf : {Γ Δ : List (NormalForm P)} → (g : G P Γ Δ) →
    {C : NormalForm P} → At Δ C → Prop where
  | identity (l : Literal P) : RightLeaf (G.identity l) (.here (.lit l) [])
  | zero (l : Literal P) : RightLeaf (G.zero l) (.here (.lit l) [])
  | top : RightLeaf (G.topI (P := P)) (.here .top [])
  | thin (Γ Δ Λ A) (f : G P Γ (Δ ++ Λ)) (ha : AtomicFormula A) :
      RightLeaf (G.thinR Γ Δ Λ A f) (At.shift Δ (.here A Λ))
  | conj {Γ Θ Δ Λ A B} (f : G P Γ (A :: Δ)) (g : G P Θ (B :: Λ)) :
      RightLeaf (G.conjR f g) (.here (.conj A B) (Δ ++ Λ))
  | disj (Γ Δ Λ A B) (f : G P Γ (Δ ++ A :: B :: Λ)) :
      RightLeaf (G.disjR Γ Δ Λ A B f) (At.shift Δ (.here (.disj A B) Λ))

/-- All possible whole-formula leaves on the left of an atomized proof. -/
inductive LeftLeaf : {Γ Δ : List (NormalForm P)} → (g : G P Γ Δ) →
    {C : NormalForm P} → At Γ C → Prop where
  | identity (l : Literal P) : LeftLeaf (G.identity l) (.here (.lit l) [])
  | zero (l : Literal P) : LeftLeaf (G.zero l) (.here (.lit l) [])
  | bot : LeftLeaf (G.botE (P := P)) (.here .bot [])
  | thin (Γ Θ Δ A) (f : G P (Γ ++ Θ) Δ) (ha : AtomicFormula A) :
      LeftLeaf (G.thinL Γ Θ Δ A f) (At.shift Γ (.here A Θ))
  | conj (Γ Θ Δ A B) (f : G P (Γ ++ A :: B :: Θ) Δ) :
      LeftLeaf (G.conjL Γ Θ Δ A B f) (At.shift Γ (.here (.conj A B) Θ))
  | disj {Γ Θ Δ Λ A B} (f : G P (A :: Γ) Δ) (g : G P (B :: Θ) Λ) :
      LeftLeaf (G.disjL f g) (.here (.disj A B) (Γ ++ Θ))

theorem rightLeaf_complete {Γ Δ : List (NormalForm P)} (f : G P Γ Δ)
    (hf : f.Atomized) {C : NormalForm P} (x : At Δ C) (hx : f.Leaf .right x) :
    RightLeaf f x := by
  cases f <;> simp only [G.Leaf, G.sourceArity] at hx
  all_goals try omega
  case identity l => cases x with
    | here => exact .identity l
    | there a => cases a
  case zero l => cases x with
    | here => exact .zero l
    | there a => cases a
  case topI => cases x with
    | here => exact .top
    | there a => cases a
  case botE => cases x
  case thinR Δ Λ A f =>
    have hi : x.index = Δ.length := by split at hx <;> omega
    cases hc : At.compare x (At.shift Δ (.here A Λ)) with
    | same => exact .thin Γ Δ Λ _ f hf.1
    | apart hn => exact False.elim (hn (hi.trans (by simp [At.index_shift,At.index])))
  case contractR A gs Λ hn f =>
    split at hx <;> omega
  case disjR Δ Λ A B f =>
    have hi : x.index = Δ.length := by split at hx <;> omega
    cases hc : At.compare x (At.shift Δ (.here (.disj A B) Λ)) with
    | same => exact .disj Γ Δ Λ A B f
    | apart hn => exact False.elim (hn (hi.trans (by simp [At.index_shift,At.index])))
  case conjR Γ Θ Δ Λ A B f g =>
    cases x with
    | here => exact .conj f g
    | there x => simp only [At.index] at hx; split at hx <;> omega

theorem leftLeaf_complete {Γ Δ : List (NormalForm P)} (g : G P Γ Δ)
    (hg : g.Atomized) {C : NormalForm P} (x : At Γ C) (hx : g.Leaf .left x) :
    LeftLeaf g x := by
  cases g <;> simp only [G.Leaf, G.sourceArity] at hx
  all_goals try omega
  case identity l => cases x with
    | here => exact .identity l
    | there a => cases a
  case zero l => cases x with
    | here => exact .zero l
    | there a => cases a
  case topI => cases x
  case botE => cases x with
    | here => exact .bot
    | there a => cases a
  case thinL Γ Θ A g =>
    have hi : x.index = Γ.length := by split at hx <;> omega
    cases hc : At.compare x (At.shift Γ (.here A Θ)) with
    | same => exact .thin Γ Θ Δ _ g hg.1
    | apart hn => exact False.elim (hn (hi.trans (by simp [At.index_shift,At.index])))
  case contractL A gs Θ hn g =>
    split at hx <;> omega
  case conjL Γ Θ A B g =>
    have hi : x.index = Γ.length := by split at hx <;> omega
    cases hc : At.compare x (At.shift Γ (.here (.conj A B) Θ)) with
    | same => exact .conj Γ Θ Δ A B g
    | apart hn => exact False.elim (hn (hi.trans (by simp [At.index_shift,At.index])))
  case disjL Γ Θ Δ Λ A B f g =>
    cases x with
    | here => exact .disj f g
    | there x => simp only [At.index] at hx; split at hx <;> omega

end DosenPetric.Reduced.Gentzen
