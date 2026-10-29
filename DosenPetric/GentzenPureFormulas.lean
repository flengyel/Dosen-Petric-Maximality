module

public import DosenPetric.GentzenPositiveNormalization

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

/-- Formulas using only one binary connective; both constants and signed literals remain. -/
def Pure (o : Op) : NormalForm P → Prop
  | .lit _ | .top | .bot => True
  | .conj A B => match o with
    | .conj => Pure o A ∧ Pure o B
    | .disj => False
  | .disj A B => match o with
    | .conj => False
    | .disj => Pure o A ∧ Pure o B

def PureContext (o : Op) (Γ : List (NormalForm P)) : Prop :=
  ∀ (C : NormalForm P), At Γ C → Pure o C

namespace PureContext
variable {o : Op} {F U : List (NormalForm P)} {A B : NormalForm P}

theorem nil : PureContext (P:=P) o [] := by intro C a; cases a

theorem cons : PureContext o (A :: U) ↔ Pure o A ∧ PureContext o U := by
  constructor
  · intro h
    exact ⟨h A (.here A U),fun C a => h C a.there⟩
  · rintro ⟨hA,hU⟩ C a
    cases a with
    | here => exact hA
    | there a => exact hU C a

theorem append : PureContext o (F ++ U) ↔ PureContext o F ∧ PureContext o U := by
  constructor
  · intro h
    exact ⟨fun C a => h C (a.before U),fun C a => h C (At.shift F a)⟩
  · rintro ⟨hF,hU⟩ C a
    cases At.cases_append F U a with
    | inl h => obtain ⟨a,rfl⟩ := h; exact hF C a
    | inr h => obtain ⟨a,rfl⟩ := h; exact hU C a

theorem pull (r : Route F U) (h : PureContext o F) : PureContext o U :=
  fun C a => h C (r.get a)

theorem components (h : PureContext o (F ++ o.formula A B :: U)) :
    PureContext o (F ++ A :: B :: U) := by
  obtain ⟨hF,hABU⟩ := append.mp h
  obtain ⟨hAB,hU⟩ := cons.mp hABU
  have hab : Pure o A ∧ Pure o B := by cases o <;> exact hAB
  exact append.mpr ⟨hF,cons.mpr ⟨hab.1,cons.mpr ⟨hab.2,hU⟩⟩⟩

end PureContext
namespace G

/-- The Gentzen mix fragment has no conjR, disjL or cut nodes. -/
def MixOnly : {Γ Δ : List (NormalForm P)} → G P Γ Δ → Prop
  | _,_,.identity _ | _,_,.zero _ | _,_,.topI | _,_,.botE => True
  | _,_,.exchangeL _ _ _ _ _ f | _,_,.exchangeR _ _ _ _ _ f
  | _,_,.thinL _ _ _ _ f | _,_,.thinR _ _ _ _ f
  | _,_,.contractL _ _ _ _ _ f | _,_,.contractR _ _ _ _ _ f
  | _,_,.conjL _ _ _ _ _ f | _,_,.disjR _ _ _ _ _ f => MixOnly f
  | _,_,.mix f g => MixOnly f ∧ MixOnly g
  | _,_,.conjR _ _ | _,_,.disjL _ _ | _,_,.cut _ _ => False

/-- Analytic cut-free proofs at pure endpoints belong to the actual mix fragment. -/
theorem mixOnly_of_pure {Γ Δ : List (NormalForm P)} (g : G P Γ Δ)
    (hc : g.CutFree) (hΓ : PureContext .conj Γ) (hΔ : PureContext .disj Δ) : g.MixOnly := by
  induction g with
  | identity => trivial
  | zero => trivial
  | topI => trivial
  | botE => trivial
  | exchangeL F X Y U Δ f ih =>
    exact ih hc (hΓ.pull (StructuralProgram.exchange F X Y U).route) hΔ
  | exchangeR Γ F X Y U f ih =>
    exact ih hc hΓ (hΔ.pull (StructuralProgram.exchange F X Y U).route)
  | thinL F U Δ A f ih => exact ih hc (hΓ.pull (Route.thin F U A)) hΔ
  | thinR Γ F U A f ih => exact ih hc hΓ (hΔ.pull (Route.thin F U A))
  | contractL A gs U Δ hn f ih => exact ih hc (hΓ.pull (copies A gs U)) hΔ
  | contractR Γ A gs U hn f ih => exact ih hc hΓ (hΔ.pull (copies A gs U))
  | conjL F U Δ A B f ih => exact ih hc hΓ.components hΔ
  | disjR Γ F U A B f ih => exact ih hc hΓ hΔ.components
  | conjR f g _ _ => exact False.elim (hΔ _ (.here _ _))
  | disjL f g _ _ => exact False.elim (hΓ _ (.here _ _))
  | mix f g ih ih' =>
    obtain ⟨hg,hf⟩ := PureContext.append.mp hΓ
    obtain ⟨kg,kf⟩ := PureContext.append.mp hΔ
    have hs := Nat.add_eq_zero_iff.mp hc
    exact ⟨ih hs.1 hf kf,ih' hs.2 hg kg⟩
  | cut f g _ _ => exact False.elim (cut_not_cutFree f g hc)

end G

/-- The pure-endpoint proposition uses the actual eliminator and yields a mix
proof, retaining both constants, signs and the complete tagged relation. -/
theorem positive_mix_represented {A B : NormalForm P} (t : Term P A B)
    (ht : t.Positive) (hA : Pure .conj A) (hB : Pure .disj B) :
    ∃ g : G P [A] [B], g.CutFree ∧ g.Atomized ∧ g.MixOnly ∧
      ofTerm g.denote = comp (rightOut .conj A) (comp (ofTerm t) (rightIn .disj B)) ∧
      ∀ (x : A.formula.Occ) (y : B.formula.Occ),
        g.relation (singletonOcc .conj A x) (singletonOcc .disj B y) ↔ t.relation x y := by
  obtain ⟨g,hg,ag,eg,rg⟩ := positive_cutFree_represented t ht
  have hp := g.mixOnly_of_pure hg
    (PureContext.cons.mpr ⟨hA,PureContext.nil⟩)
    (PureContext.cons.mpr ⟨hB,PureContext.nil⟩)
  exact ⟨g,hg,ag,hp,eg,rg⟩

end DosenPetric.Reduced.Gentzen
