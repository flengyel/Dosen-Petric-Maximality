module

public import DosenPetric.GentzenBlockedPatterns
public import DosenPetric.GentzenProofReplacement
public import DosenPetric.GentzenSelectionOrigins

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

namespace G

theorem ruleKind_reindex {Γ Δ Γ' Δ' : List (NormalForm P)} (hΓ : Γ = Γ') (hΔ : Δ = Δ')
    (g : G P Γ Δ) : (g.reindex hΓ hΔ).ruleKind = g.ruleKind := by cases hΓ; cases hΔ; rfl

def contractedPremiseKind : {Γ Δ : List (NormalForm P)} → G P Γ Δ → Option RuleKind
  | _,_,.contractL _ _ _ _ _ f | _,_,.contractR _ _ _ _ _ f => some f.ruleKind
  | _,_,_ => none
end G

theorem BlockedL.premise_kind {Γ Δ : List (NormalForm P)} {g : G P Γ Δ} (h : BlockedL g) :
    g.contractedPremiseKind ∈ [some .mix,some .conjR,some .exchangeL,some .conjL] := by
  cases h <;> simp only [BlockedSource.left2,BlockedSource.left3,G.contractedPremiseKind,G.ruleKind_reindex]
  all_goals try simp only [BlockedSource.disjLLast,BlockedSource.conjLLast,G.ruleKind_reindex]
  all_goals simp [G.ruleKind]

theorem BlockedR.premise_kind {Γ Δ : List (NormalForm P)} {g : G P Γ Δ} (h : BlockedR g) :
    g.contractedPremiseKind ∈ [some .mix,some .exchangeL,some .conjR,some .disjR] := by
  cases h <;> simp only [BlockedSource.right2,BlockedSource.right3,G.contractedPremiseKind,G.ruleKind_reindex]
  all_goals try simp only [BlockedSource.disjLLast,G.ruleKind_reindex]
  all_goals simp [G.ruleKind]

namespace ProofAddress
variable {Γ Δ Θ Λ Ξ Ω : List (NormalForm P)}
variable {root : G P Γ Δ} {g : G P Θ Λ} {h : G P Ξ Ω}

/-- Proper containment is witnessed by a nonempty typed suffix address. -/
def ProperContains (a : ProofAddress root g) (b : ProofAddress root h) : Prop :=
  ∃ c : ProofAddress g h, c.path ≠ [] ∧ a.append c = b

theorem proper_length {a : ProofAddress root g} {b : ProofAddress root h}
    (hab : a.ProperContains b) : a.path.length < b.path.length := by
  obtain ⟨c,hc,he⟩ := hab
  have hp := congrArg (fun d => d.path.length) he
  rw [append_path,List.length_append] at hp
  have hl : 0 < c.path.length := List.length_pos_iff.mpr hc
  omega

theorem proper_irrefl (a : ProofAddress root g) : ¬ a.ProperContains a := by
  intro he
  have hh := proper_length he
  omega

theorem proper_trans {I J : List (NormalForm P)} {k : G P I J}
    {a : ProofAddress root g} {b : ProofAddress root h} {c : ProofAddress root k}
    (hab : a.ProperContains b) (hbc : b.ProperContains c) : a.ProperContains c := by
  obtain ⟨d,hd,he⟩ := hab
  obtain ⟨e,_,hf⟩ := hbc
  refine ⟨d.append e,?_,?_⟩
  · intro hn
    have hl := congrArg List.length hn
    rw [append_path,List.length_append] at hl
    have hp := List.length_pos_iff.mpr hd
    simp only [List.length_nil] at hl
    omega
  · rw [← append_assoc,he,hf]

theorem down_proper (a : ProofAddress root g) (p : Premise g h) : a.ProperContains (a.down p) :=
  by
    refine Exists.intro (ProofAddress.root.down p) ?_
    constructor
    · intro he
      cases he
    · rfl

/-- The selected whole-formula position and proof branch path are both retained. -/
def traceAt (a : ProofAddress root g) (s : SequentSide) {C : NormalForm P}
    (x : Place s Θ Λ C) : TraceNode P s C := ⟨Θ,Λ,g,a.path,x⟩

end ProofAddress

section Left
variable {Γ Θ Δ Λ : List (NormalForm P)} {C : NormalForm P}
variable (f : G P Γ (C::Δ)) (g : G P (C::Θ) Λ)

/-- Source reducibility of a tied left contraction in the right cut-premise.
    Only proper containing tied contractions are required to be blocked. -/
def ReducibleL {U V : List (NormalForm P)} {w : G P U V}
    (a : ProofAddress g w) (x : At U C) : Prop :=
  G.Topmost f g ∧ g.TiedRight (a.traceAt .left x) ∧ ¬ BlockedL w ∧
    ∀ {I J : List (NormalForm P)} {v : G P I J}
      (b : ProofAddress g v) (y : At I C),
      g.TiedRight (b.traceAt .left y) → b.ProperContains a → BlockedL v

theorem ReducibleL.cutFree {U V : List (NormalForm P)} {w : G P U V}
    {a : ProofAddress g w} {x : At U C} (h : ReducibleL f g a x) : w.CutFree :=
  a.cutFree h.1.2

theorem ReducibleL.incomparable {U V I J : List (NormalForm P)}
    {w : G P U V} {v : G P I J} {a : ProofAddress g w} {b : ProofAddress g v}
    {x : At U C} {y : At I C} (ha : ReducibleL f g a x) (hb : ReducibleL f g b y) :
    ¬ b.ProperContains a := fun he => hb.2.2.1 (ha.2.2.2 b y hb.2.1 he)
end Left

section Right
variable {Γ Θ Δ Λ : List (NormalForm P)} {C : NormalForm P}
variable (f : G P Γ (C::Δ)) (g : G P (C::Θ) Λ)

/-- Separately typed source reducibility of a right contraction in the left premise. -/
def ReducibleR {U V : List (NormalForm P)} {w : G P U V}
    (a : ProofAddress f w) (x : At V C) : Prop :=
  G.Topmost f g ∧ f.TiedLeft (a.traceAt .right x) ∧ ¬ BlockedR w ∧
    ∀ {I J : List (NormalForm P)} {v : G P I J}
      (b : ProofAddress f v) (y : At J C),
      f.TiedLeft (b.traceAt .right y) → b.ProperContains a → BlockedR v

theorem ReducibleR.cutFree {U V : List (NormalForm P)} {w : G P U V}
    {a : ProofAddress f w} {x : At V C} (h : ReducibleR f g a x) : w.CutFree :=
  a.cutFree h.1.1

theorem ReducibleR.incomparable {U V I J : List (NormalForm P)}
    {w : G P U V} {v : G P I J} {a : ProofAddress f w} {b : ProofAddress f v}
    {x : At V C} {y : At J C} (ha : ReducibleR f g a x) (hb : ReducibleR f g b y) :
    ¬ b.ProperContains a := fun he => hb.2.2.1 (ha.2.2.2 b y hb.2.1 he)
end Right

end DosenPetric.Reduced.Gentzen
