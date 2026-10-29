module

public import DosenPetric.SemanticSourceModel
public import DosenPetric.PresentationFragmentMaximality

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.PresentationSemantics
universe u v w
variable {X : Type u} {C : Category.{u,v} X} {O : Objects X}
  (S : Primitives C O) (P : Type w)

/-- Agreement under the entire family of full-signature interpretations. -/
def Agreement {A B : Formula P} (f g : Presentation.Hom A B) : Prop :=
  ∀ F : Interpretation S P, F.map f = F.map g

namespace Agreement
variable {S P}

theorem refl {A B : Formula P} (f : Presentation.Hom A B) : Agreement S P f f := fun _ => rfl
theorem symm {A B : Formula P} {f g : Presentation.Hom A B}
    (h : Agreement S P f g) : Agreement S P g f := fun F => (h F).symm
theorem trans {A B : Formula P} {f g h : Presentation.Hom A B}
    (hfg : Agreement S P f g) (hgh : Agreement S P g h) : Agreement S P f h :=
  fun F => (hfg F).trans (hgh F)

theorem comp {A B D : Formula P} {f f' : Presentation.Hom A B} {g g' : Presentation.Hom B D}
    (hf : Agreement S P f f') (hg : Agreement S P g g') :
    Agreement S P (Presentation.comp f g) (Presentation.comp f' g') := by
  intro F
  exact (F.toFunctor.map_comp f g).trans
    (((congrArg (fun k => C.comp k (F.map g)) (hf F)).trans
      (congrArg (fun k => C.comp (F.map f') k) (hg F))).trans
      (F.toFunctor.map_comp f' g').symm)

theorem tensor (o : Presentation.Op) {A B D E : Formula P}
    {f f' : Presentation.Hom A D} {g g' : Presentation.Hom B E}
    (hf : Agreement S P f f') (hg : Agreement S P g g') :
    Agreement S P (Presentation.tensor o f g) (Presentation.tensor o f' g') := by
  intro F
  have h := F.map_tensor o f g
  rw [hf F,hg F] at h
  exact eq_of_heq (h.trans (F.map_tensor o f' g').symm)

def fragment : Congruence (Presentation.operations P) where
  Rel := Agreement S P
  refl := refl
  symm := symm
  trans := trans
  comp := comp
  pair {Y A B f f' g g'} hf hg := by
    change Agreement S P (Presentation.pair f g) (Presentation.pair f' g')
    exact comp (refl (Presentation.diag Y)) (tensor .conj hf hg)
  copair hf hg := comp (tensor .disj hf hg) (refl _)

theorem fragment_closed : (Presentation.substitution P).Closed (fragment (S:=S) (P:=P)) := by
  intro σ A B f g h F
  exact h (F.precompose σ)

/-- Full congruence closure follows from the already proved fragment dichotomy;
no closure of one fixed interpretation's kernel is asserted. -/
def congruence : Presentation.ProofCongruence P :=
  .of_closed_fragment (fragment (S:=S) (P:=P)) (fragment_closed (S:=S) (P:=P))

theorem closed : (congruence (S:=S) (P:=P)).Closed := fragment_closed (S:=S) (P:=P)

theorem iff_valuations (law : S.SatisfiesTheory P) {A B : Formula P}
    (f g : Presentation.Hom A B) : Agreement S P f g ↔
    ∀ α : P → X, S.evaluateHom law α f = S.evaluateHom law α g := by
  constructor
  · intro h α
    exact h (S.canonicalInterpretation law α)
  · intro h F
    exact eq_of_heq ((F.hom_evaluation law f).trans
      ((heq_of_eq (h F.valuation)).trans (F.hom_evaluation law g).symm))

end Agreement
end DosenPetric.PresentationSemantics
