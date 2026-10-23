module

public import DosenPetric.GentzenRules
public import DosenPetric.PresentationConsistency

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u

/-- Proof trees with cuts visible and only atomic identity/zero leaves. -/
inductive G (P : Type u) : List (NormalForm P) → List (NormalForm P) → Type u where
  | identity (l : Literal P) : G P [.lit l] [.lit l]
  | zero (l : Literal P) : G P [.lit l] [.lit l]
  | topI : G P [] [.top]
  | botE : G P [.bot] []
  | exchangeL (Γ X Y Θ Δ) : G P (Γ ++ X ++ Y ++ Θ) Δ → G P (Γ ++ Y ++ X ++ Θ) Δ
  | exchangeR (Γ Δ X Y Λ) : G P Γ (Δ ++ X ++ Y ++ Λ) → G P Γ (Δ ++ Y ++ X ++ Λ)
  | thinL (Γ Θ Δ A) : G P (Γ ++ Θ) Δ → G P (Γ ++ A :: Θ) Δ
  | thinR (Γ Δ Λ A) : G P Γ (Δ ++ Λ) → G P Γ (Δ ++ A :: Λ)
  | contractL (C gs Θ Δ) : 2 ≤ gs.length →
      G P (repeated C gs ++ Θ) Δ → G P (gaps gs ++ C :: Θ) Δ
  | contractR (Γ C gs Λ) : 2 ≤ gs.length →
      G P Γ (repeated C gs ++ Λ) → G P Γ (gaps gs ++ C :: Λ)
  | conjL (Γ Θ Δ A B) : G P (Γ ++ A :: B :: Θ) Δ → G P (Γ ++ .conj A B :: Θ) Δ
  | disjR (Γ Δ Λ A B) : G P Γ (Δ ++ A :: B :: Λ) → G P Γ (Δ ++ .disj A B :: Λ)
  | conjR {Γ Θ Δ Λ A B} : G P Γ (A :: Δ) → G P Θ (B :: Λ) →
      G P (Γ ++ Θ) (.conj A B :: (Δ ++ Λ))
  | disjL {Γ Θ Δ Λ A B} : G P (A :: Γ) Δ → G P (B :: Θ) Λ →
      G P (.disj A B :: (Γ ++ Θ)) (Δ ++ Λ)
  | mix {Γ Θ Δ Λ} : G P Γ Δ → G P Θ Λ → G P (Θ ++ Γ) (Λ ++ Δ)
  | cut {Γ Θ Δ Λ C} : G P Γ (C :: Δ) → G P (C :: Θ) Λ →
      G P (Θ ++ Γ) (Λ ++ Δ)

namespace G
variable {P : Type u}

def denote : {Γ Δ : List (NormalForm P)} → G P Γ Δ → Term P (ante Γ) (succ Δ)
  | _, _, .identity l => encode (.id (.lit l))
  | _, _, .zero l => encode (.zero (.lit l))
  | _, _, .topI => .rightIn .disj .top
  | _, _, .botE => .rightOut .conj .bot
  | _, _, .exchangeL Γ X Y Θ _ f => .comp (exchange .conj Γ X Y Θ).invTerm f.denote
  | _, _, .exchangeR _ Δ X Y Λ f => .comp f.denote (exchange .disj Δ X Y Λ).toTerm
  | _, _, .thinL Γ Θ _ A f => .comp (Route.thin Γ Θ A).product f.denote
  | _, _, .thinR _ Δ Λ A f => .comp f.denote (Route.thin Δ Λ A).coproduct
  | _, _, .contractL C gs Θ _ _ f => .comp (copies C gs Θ).product f.denote
  | _, _, .contractR _ C gs Λ _ f => .comp f.denote (copies C gs Λ).coproduct
  | _, _, .conjL Γ Θ _ A B f => .comp (Rules.conjLeft Γ Θ A B).toTerm f.denote
  | _, _, .disjR _ Δ Λ A B f => .comp f.denote (Rules.disjRight Δ Λ A B).toTerm
  | _, _, .conjR f g => Rules.conjRight f.denote g.denote
  | _, _, .disjL f g => Rules.disjLeft f.denote g.denote
  | _, _, .mix f g => Rules.mix f.denote g.denote
  | _, _, .cut f g => Rules.cut f.denote g.denote

theorem denote_positive {Γ Δ : List (NormalForm P)} (g : G P Γ Δ) : g.denote.Positive := by
  induction g with
  | identity => exact .comp (.rightOut ..) (.comp (.id _) (.rightIn ..))
  | zero => exact .comp (.rightOut ..) (.comp (.zero _) (.rightIn ..))
  | topI => exact .rightIn ..
  | botE => exact .rightOut ..
  | exchangeL _ _ _ _ _ _ ih => exact .comp (exchange ..).positive_inv ih
  | exchangeR _ _ _ _ _ _ ih => exact .comp ih (exchange ..).positive_to
  | thinL _ _ _ _ _ ih => exact .comp (Route.product_positive _) ih
  | thinR _ _ _ _ _ ih => exact .comp ih (Route.coproduct_positive _)
  | contractL _ _ _ _ _ _ ih => exact .comp (Route.product_positive _) ih
  | contractR _ _ _ _ _ _ ih => exact .comp ih (Route.coproduct_positive _)
  | conjL _ _ _ _ _ _ ih => exact .comp (Rules.conjLeft ..).positive_to ih
  | disjR _ _ _ _ _ _ ih => exact .comp ih (Rules.disjRight ..).positive_to
  | conjR _ _ ih ih' => exact Rules.conjRight_positive ih ih'
  | disjL _ _ ih ih' => exact Rules.disjLeft_positive ih ih'
  | mix _ _ ih ih' => exact Rules.mix_positive ih ih'
  | cut _ _ ih ih' => exact Rules.cut_positive ih ih'

/-- Count every syntactic cut, including cuts inside structural/logical premises. -/
def cutCount : {Γ Δ : List (NormalForm P)} → G P Γ Δ → Nat
  | _, _, .identity _ | _, _, .zero _ | _, _, .topI | _, _, .botE => 0
  | _, _, .exchangeL _ _ _ _ _ f | _, _, .exchangeR _ _ _ _ _ f
  | _, _, .thinL _ _ _ _ f | _, _, .thinR _ _ _ _ f
  | _, _, .contractL _ _ _ _ _ f | _, _, .contractR _ _ _ _ _ f
  | _, _, .conjL _ _ _ _ _ f | _, _, .disjR _ _ _ _ _ f => f.cutCount
  | _, _, .conjR f g | _, _, .disjL f g | _, _, .mix f g => f.cutCount + g.cutCount
  | _, _, .cut f g => f.cutCount + g.cutCount + 1

def CutFree {Γ Δ : List (NormalForm P)} (g : G P Γ Δ) : Prop := g.cutCount = 0

theorem cut_not_cutFree {Γ Θ Δ Λ : List (NormalForm P)} {C : NormalForm P}
    (f : G P Γ (C :: Δ)) (g : G P (C :: Θ) Λ) : ¬ (G.cut f g).CutFree := by
  simp [CutFree, cutCount]

def relation {Γ Δ : List (NormalForm P)} (g : G P Γ Δ) := g.denote.relation

theorem occurrence_denote {Γ Δ : List (NormalForm P)} (g : G P Γ Δ) :
    occurrenceMap (ofTerm g.denote) = g.relation := rfl

/-- The two differently coloured empty contexts cannot support a proof tree. -/
theorem no_empty (g : G P [] []) : False := Presentation.empty_hom P ⟨inclusion (ofTerm g.denote)⟩

end G
end DosenPetric.Reduced.Gentzen
