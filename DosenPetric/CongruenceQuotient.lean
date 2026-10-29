module

public import DosenPetric.CategoryFunctor
public import DosenPetric.Structure

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Congruence
universe u v
variable {P : Type u} {C : Category.{u,v} (Formula P)} {S : Structure C} (Q : Congruence S)

def homSetoid (A B : Formula P) : Setoid (C.Hom A B) where
  r := Q.Rel
  iseqv := ⟨Q.refl,Q.symm,Q.trans⟩
abbrev QuotientHom (A B : Formula P) := Quotient (Q.homSetoid A B)
def classOf {A B : Formula P} (f : C.Hom A B) : Q.QuotientHom A B := Quotient.mk _ f

def quotientComp {A B D : Formula P} (f : Q.QuotientHom A B) (g : Q.QuotientHom B D) : Q.QuotientHom A D :=
  Quotient.liftOn₂ f g (fun f g => Q.classOf (C.comp f g))
    (fun _ _ _ _ hf hg => Quotient.sound (Q.comp hf hg))

def quotientCategory : Category (Formula P) where
  Hom := Q.QuotientHom
  id A := Q.classOf (C.id A)
  comp := Q.quotientComp
  id_comp f := by
    induction f using Quotient.inductionOn with
    | h f => exact congrArg Q.classOf (C.id_comp f)
  comp_id f := by
    induction f using Quotient.inductionOn with
    | h f => exact congrArg Q.classOf (C.comp_id f)
  assoc f g h := by
    induction f using Quotient.inductionOn with | h f =>
    induction g using Quotient.inductionOn with | h g =>
    induction h using Quotient.inductionOn with | h h => exact congrArg Q.classOf (C.assoc f g h)

def quotientFunctor : Functor C Q.quotientCategory where
  obj := _root_.id
  map := Q.classOf
  map_id _ := rfl
  map_comp _ _ := rfl

def quotientPair {X A B : Formula P} (f : Q.QuotientHom X A) (g : Q.QuotientHom X B) :
    Q.QuotientHom X (.conj A B) :=
  Quotient.liftOn₂ f g (fun f g => Q.classOf (S.pair f g))
    (fun _ _ _ _ hf hg => Quotient.sound (Q.pair hf hg))

def quotientCopair {A B X : Formula P} (f : Q.QuotientHom A X) (g : Q.QuotientHom B X) :
    Q.QuotientHom (.disj A B) X :=
  Quotient.liftOn₂ f g (fun f g => Q.classOf (S.copair f g))
    (fun _ _ _ _ hf hg => Quotient.sound (Q.copair hf hg))

/-- Products, coproducts and both units descend to equivalence classes with all
beta/eta equations. No previously empty hom-set is made inhabited. -/
def quotientStructure : Structure Q.quotientCategory where
  fst A B := Q.classOf (S.fst A B)
  snd A B := Q.classOf (S.snd A B)
  pair := Q.quotientPair
  pair_fst f g := by
    induction f using Quotient.inductionOn with | h f =>
    induction g using Quotient.inductionOn with | h g => exact congrArg Q.classOf (S.pair_fst f g)
  pair_snd f g := by
    induction f using Quotient.inductionOn with | h f =>
    induction g using Quotient.inductionOn with | h g => exact congrArg Q.classOf (S.pair_snd f g)
  pair_eta f := by
    induction f using Quotient.inductionOn with | h f => exact congrArg Q.classOf (S.pair_eta f)
  inl A B := Q.classOf (S.inl A B)
  inr A B := Q.classOf (S.inr A B)
  copair := Q.quotientCopair
  inl_copair f g := by
    induction f using Quotient.inductionOn with | h f =>
    induction g using Quotient.inductionOn with | h g => exact congrArg Q.classOf (S.inl_copair f g)
  inr_copair f g := by
    induction f using Quotient.inductionOn with | h f =>
    induction g using Quotient.inductionOn with | h g => exact congrArg Q.classOf (S.inr_copair f g)
  copair_eta f := by
    induction f using Quotient.inductionOn with | h f => exact congrArg Q.classOf (S.copair_eta f)
  toTop A := Q.classOf (S.toTop A)
  toTop_unique f := by
    induction f using Quotient.inductionOn with | h f => exact congrArg Q.classOf (S.toTop_unique f)
  fromBot A := Q.classOf (S.fromBot A)
  fromBot_unique f := by
    induction f using Quotient.inductionOn with | h f => exact congrArg Q.classOf (S.fromBot_unique f)
  dist A B D := Q.classOf (S.dist A B D)

def quotientZeroIdentity (Z : ZeroIdentity C) : ZeroIdentity Q.quotientCategory where
  zero A := Q.classOf (Z.zero A)
  law f g := by
    induction f using Quotient.inductionOn with | h f =>
    induction g using Quotient.inductionOn with | h g => exact congrArg Q.classOf (Z.law f g)

theorem quotient_thin_iff_total : (∀ A B, Subsingleton (Q.QuotientHom A B)) ↔ Q.Total := by
  constructor
  · intro h A B f g
    exact Quotient.exact ((h A B).allEq (Q.classOf f) (Q.classOf g))
  · intro h A B
    constructor
    intro f g
    induction f using Quotient.inductionOn with | h f =>
    induction g using Quotient.inductionOn with | h g => exact Quotient.sound (h f g)

theorem quotient_preserves_empty {A B : Formula P} (h : ¬ Nonempty (C.Hom A B)) :
    ¬ Nonempty (Q.QuotientHom A B) := by
  intro ⟨f⟩
  induction f using Quotient.inductionOn with | h f => exact h ⟨f⟩

end DosenPetric.Congruence
