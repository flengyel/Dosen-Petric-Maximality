module

public import DosenPetric.OriginalIsolation

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric
universe u v

/-- Evaluation and the beta/eta universal property of an exponential for the
specified products. No exponential is supplied for the intended source category. -/
structure ExponentialData {P : Type u} {C : Category.{u,v} (Formula P)}
    (S : Structure C) (A B : Formula P) where
  object : Formula P
  evaluation : C.Hom (.conj object A) B
  curry : ∀ {X}, C.Hom (.conj X A) B → C.Hom X object
  beta : ∀ {X} (f : C.Hom (.conj X A) B),
    C.comp (S.prodMap (curry f) (C.id A)) evaluation = f
  eta : ∀ {X} (h : C.Hom X object),
    curry (C.comp (S.prodMap h (C.id A)) evaluation) = h

namespace ExponentialData
variable {P : Type u} {C : Category.{u,v} (Formula P)} {S : Structure C}

theorem hom_unique {A B : Formula P} (E : ExponentialData S A B)
    (points : ∀ X (f g : C.Hom .top X), f = g) (f g : C.Hom A B) : f = g := by
  have hc := points E.object (E.curry (C.comp (S.snd .top A) f))
    (E.curry (C.comp (S.snd .top A) g))
  have he := congrArg (fun h => C.comp (S.prodMap h (C.id A)) E.evaluation) hc
  rw [E.beta,E.beta] at he
  have hh := congrArg (fun h => C.comp (S.pair (S.toTop A) (C.id A)) h) he
  simpa only [← C.assoc,S.pair_snd,C.id_comp] using hh

end ExponentialData
namespace Presentation
variable {P : Type u}

/-- The two distinct projections already prevent this particular exponential. -/
theorem no_projection_exponential (p : P) :
    ¬ Nonempty (ExponentialData (operations P) (.conj (.var p) (.var p)) (.var p)) := by
  intro h
  obtain ⟨E⟩ := h
  exact nonthin p (E.hom_unique (fun _ f g => fromTop_unique f g)
    (fst (.var p) (.var p)) (snd (.var p) (.var p)))

/-- The source category admits no cartesian closed structure with these products. -/
theorem not_cartesian_closed (p : P) :
    ¬ (∀ A B : Formula P, Nonempty (ExponentialData (operations P) A B)) := by
  intro h
  exact no_projection_exponential p (h (.conj (.var p) (.var p)) (.var p))

end Presentation
end DosenPetric
