module

public import DosenPetric.SemanticUniversalAgreement

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.PresentationSemantics
universe u v w
variable {X : Type u} {C : Category.{u,v} X} {O : Objects X}
  {S : Primitives C O} {P : Type w}

/-- The model corollary for the complete source presentation. The conclusion
quantifies over all native target arrows, not just images of source arrows. -/
theorem model_corollary [Nonempty P] (M : Model P S)
    {A B : Formula P} (f g : Presentation.Hom A B) (hne : f ≠ g)
    (hfg : ∀ α : P → X, S.evaluateHom M.equations α f = S.evaluateHom M.equations α g) :
    ∀ {Y Z : X} (a b : C.Hom Y Z), a = b := by
  have h := (Agreement.iff_valuations M.equations f g).mpr hfg
  have ht : (Agreement.congruence (S:=S) (P:=P)).Total :=
    Presentation.maximality Agreement.congruence Agreement.closed f g hne h
  obtain ⟨p⟩ := ‹Nonempty P›
  intro Y Z a b
  let α : P → X := fun _ => Z
  have hp := ht (Presentation.fst (.var p) (.var p)) (Presentation.snd (.var p) (.var p))
    (S.canonicalInterpretation M.equations α)
  change S.fst Z Z = S.snd Z Z at hp
  have he := congrArg (fun k => C.comp (S.pair a b) k) hp
  rw [M.bicartesian.pair_fst,M.bicartesian.pair_snd] at he
  exact he

/-- The equivalent formulation using all full-signature interpretations. -/
theorem model_corollary_interpretations [Nonempty P] (M : Model P S)
    {A B : Formula P} (f g : Presentation.Hom A B) (hne : f ≠ g)
    (hfg : Agreement S P f g) : ∀ {Y Z : X} (a b : C.Hom Y Z), a = b :=
  model_corollary M f g hne ((Agreement.iff_valuations M.equations f g).mp hfg)

end DosenPetric.PresentationSemantics
