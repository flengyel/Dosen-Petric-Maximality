module

public import DosenPetric.GentzenMirrorBinaryResidual
public import DosenPetric.GentzenMirrorInterpretation
public import DosenPetric.GentzenBlockedGammaConj

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.MirrorCalculus
universe u
variable {P : Type u}

def diag (A : NormalForm P) : Hom A (.conj A A) := Reduced.codiag (mirror A)
def codiag (A : NormalForm P) : Hom (.disj A A) A := Reduced.diag (mirror A)
def inl (A B : NormalForm P) : Hom A (.disj A B) := Reduced.snd (mirror B) (mirror A)
def copair {A B X : NormalForm P} (f : Hom A X) (g : Hom B X) : Hom (.disj A B) X :=
  Reduced.pair g f

theorem disj_ext {A B X : NormalForm P} (f g : Hom (.disj A B) X)
    (h₁ : comp (inl A B) f = comp (inl A B) g)
    (h₂ : comp (inr A B) f = comp (inr A B) g) : f = g :=
  Reduced.conj_ext f g h₂ h₁

theorem pair_def {X A B : NormalForm P} (f : Hom X A) (g : Hom X B) :
    pair f g = comp (diag X) (tensor .conj f g) := rfl

theorem pair_tensor {X A B D E : NormalForm P}
    (f : Hom X A) (g : Hom X B) (h : Hom A D) (k : Hom B E) :
    comp (pair f g) (tensor .conj h k) = pair (comp f h) (comp g k) := by
  apply ProductCalculation.ext
  · rw [ProductCalculation.pair_fst,Laws.assoc,← Laws.fst_nat,
      ← Laws.assoc,ProductCalculation.pair_fst]
  · rw [ProductCalculation.pair_snd,Laws.assoc,← Laws.snd_nat,
      ← Laws.assoc,ProductCalculation.pair_snd]

theorem copair_post {A B X Y : NormalForm P} (f : Hom A X) (g : Hom B X)
    (k : Hom X Y) : comp (copair f g) k = copair (comp f k) (comp g k) :=
  Gentzen.ProductCalculation.pair_pre k g f

theorem tensor_copair {A B D E X : NormalForm P}
    (f : Hom A D) (g : Hom B E) (h : Hom D X) (k : Hom E X) :
    comp (tensor .disj f g) (copair h k) = copair (comp f h) (comp g k) :=
  Gentzen.BlockedMix.pair_tensor k h g f

theorem copair_eta {A B X : NormalForm P} (f : Hom (.disj A B) X) :
    copair (comp (inl A B) f) (comp (inr A B) f) = f :=
  (conjDiagonal P).pair_eta f

namespace Laws

theorem inl_nat {A B D E : NormalForm P} (f : Hom A D) (g : Hom B E) :
    comp (inl A B) (tensor .disj f g) = comp f (inl D E) :=
  (Reduced.Laws.snd_nat g f).symm

theorem inr_nat {A B D E : NormalForm P} (f : Hom A D) (g : Hom B E) :
    comp (inr A B) (tensor .disj f g) = comp g (inr D E) :=
  (Reduced.Laws.fst_nat g f).symm

theorem diag_mix_codiag (A : NormalForm P) :
    comp (diag A) (comp (mix A A) (codiag A)) = id A := by
  simpa only [comp,diag,codiag,mix,id,Reduced.Laws.assoc] using
    Reduced.Laws.diag_mix_codiag (mirror A)

end Laws

/-- The reflected residual branch is the actual source projection equation. -/
theorem mixedDisj_inr (A B X Y : NormalForm P) :
    comp (tensor .conj (inr A X) (inr B Y)) (mixedDisj A X B Y) =
      comp (mix X Y) (inr (.conj A B) (.disj X Y)) := by
  rw [MirrorInterpretation.mixed_source]
  exact Gentzen.sourceConj_fst (mirror Y) (mirror X) (mirror B) (mirror A)

namespace BlockedMix

def sharedInput {Y F H X : NormalForm P} (p : Hom Y F) (q : Hom Y H) :
    Hom (.conj Y X) (.conj (.conj H X) (.conj F X)) :=
  pair (tensor .conj q (id X)) (tensor .conj p (id X))

def sharedOutput (E D R : NormalForm P) :
    Hom (.disj (.disj E R) (.disj D R)) (.disj (.disj E D) R) :=
  copair (tensor .disj (inl E D) (id R)) (tensor .disj (inr E D) (id R))

end BlockedMix
end DosenPetric.Reduced.Gentzen.MirrorCalculus
