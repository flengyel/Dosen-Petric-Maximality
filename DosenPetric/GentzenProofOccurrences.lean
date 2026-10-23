module

public import DosenPetric.GentzenTraceFibers

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

namespace G

/-- Proof-node count is used only to justify finite tracing recursion. -/
def proofSize : {Γ Δ : List (NormalForm P)} → G P Γ Δ → Nat
  | _,_, .identity _ | _,_, .zero _ | _,_, .topI | _,_, .botE => 1
  | _,_, .exchangeL _ _ _ _ _ f | _,_, .exchangeR _ _ _ _ _ f
  | _,_, .thinL _ _ _ _ f | _,_, .thinR _ _ _ _ f
  | _,_, .contractL _ _ _ _ _ f | _,_, .contractR _ _ _ _ _ f
  | _,_, .conjL _ _ _ _ _ f | _,_, .disjR _ _ _ _ _ f => f.proofSize + 1
  | _,_, .conjR f g | _,_, .disjL f g | _,_, .mix f g | _,_, .cut f g => f.proofSize + g.proofSize + 1

end G

/-- A particular premise occurrence of a rule; the two binary branches stay distinct. -/
inductive Premise : {Γ Δ : List (NormalForm P)} → G P Γ Δ →
    {Θ Λ : List (NormalForm P)} → G P Θ Λ → Type u where
  | exchangeL (Γ X Y Θ Δ) (f : G P (Γ ++ X ++ Y ++ Θ) Δ) : Premise (.exchangeL Γ X Y Θ Δ f) f
  | exchangeR (Γ Δ X Y Λ) (f : G P Γ (Δ ++ X ++ Y ++ Λ)) : Premise (.exchangeR Γ Δ X Y Λ f) f
  | thinL (Γ Θ Δ A) (f : G P (Γ ++ Θ) Δ) : Premise (.thinL Γ Θ Δ A f) f
  | thinR (Γ Δ Λ A) (f : G P Γ (Δ ++ Λ)) : Premise (.thinR Γ Δ Λ A f) f
  | contractL (C gs Θ Δ hn) (f : G P (repeated C gs ++ Θ) Δ) : Premise (.contractL C gs Θ Δ hn f) f
  | contractR (Γ C gs Λ hn) (f : G P Γ (repeated C gs ++ Λ)) : Premise (.contractR Γ C gs Λ hn f) f
  | conjL (Γ Θ Δ A B) (f : G P (Γ ++ A :: B :: Θ) Δ) : Premise (.conjL Γ Θ Δ A B f) f
  | disjR (Γ Δ Λ A B) (f : G P Γ (Δ ++ A :: B :: Λ)) : Premise (.disjR Γ Δ Λ A B f) f
  | conjR_left {Γ Θ Δ Λ A B} (f : G P Γ (A :: Δ)) (g : G P Θ (B :: Λ)) : Premise (.conjR f g) f
  | conjR_right {Γ Θ Δ Λ A B} (f : G P Γ (A :: Δ)) (g : G P Θ (B :: Λ)) : Premise (.conjR f g) g
  | disjL_left {Γ Θ Δ Λ A B} (f : G P (A :: Γ) Δ) (g : G P (B :: Θ) Λ) : Premise (.disjL f g) f
  | disjL_right {Γ Θ Δ Λ A B} (f : G P (A :: Γ) Δ) (g : G P (B :: Θ) Λ) : Premise (.disjL f g) g
  | mix_left {Γ Θ Δ Λ} (f : G P Γ Δ) (g : G P Θ Λ) : Premise (.mix f g) f
  | mix_right {Γ Θ Δ Λ} (f : G P Γ Δ) (g : G P Θ Λ) : Premise (.mix f g) g
  | cut_left {Γ Θ Δ Λ C} (f : G P Γ (C :: Δ)) (g : G P (C :: Θ) Λ) : Premise (.cut f g) f
  | cut_right {Γ Θ Δ Λ C} (f : G P Γ (C :: Δ)) (g : G P (C :: Θ) Λ) : Premise (.cut f g) g

namespace Premise

def branch {Γ Δ Θ Λ : List (NormalForm P)} {f : G P Γ Δ} {g : G P Θ Λ} : Premise f g → Nat
  | .conjR_right .. | .disjL_right .. | .mix_right .. | .cut_right .. => 1
  | _ => 0

theorem proofSize_lt {Γ Δ Θ Λ : List (NormalForm P)} {f : G P Γ Δ} {g : G P Θ Λ}
    (p : Premise f g) : g.proofSize < f.proofSize := by
  cases p <;> simp only [G.proofSize] <;> omega

end Premise

/-- A proof occurrence, not merely a subterm value. -/
inductive ProofAddress {Γ Δ : List (NormalForm P)} (root : G P Γ Δ) :
    {Θ Λ : List (NormalForm P)} → G P Θ Λ → Type u where
  | root : ProofAddress root root
  | down {Θ Λ Ξ Ω} {f : G P Θ Λ} {g : G P Ξ Ω} :
      ProofAddress root f → Premise f g → ProofAddress root g

namespace ProofAddress

def path {Γ Δ Θ Λ : List (NormalForm P)} {root : G P Γ Δ} {g : G P Θ Λ} :
    ProofAddress root g → List Nat
  | .root => []
  | .down a p => a.path ++ [p.branch]

theorem down_path {Γ Δ Θ Λ Ξ Ω : List (NormalForm P)} {root : G P Γ Δ}
    {f : G P Θ Λ} {g : G P Ξ Ω} (a : ProofAddress root f) (p : Premise f g) :
    (a.down p).path = a.path ++ [p.branch] := rfl

end ProofAddress
end DosenPetric.Reduced.Gentzen
