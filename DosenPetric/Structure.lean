module

public import DosenPetric.Category
public import DosenPetric.Formula
public import DosenPetric.Relations

@[expose] public section

set_option autoImplicit false

namespace DosenPetric

universe u v

/-- The bicartesian operations and distributor used in contextual collapse.
The objects are formulas; no presentation of the arrows is asserted. -/
structure Structure {P : Type u} (C : Category.{u,v} (Formula P)) where
  fst : (A B : Formula P) → C.Hom (.conj A B) A
  snd : (A B : Formula P) → C.Hom (.conj A B) B
  pair : {X A B : Formula P} → C.Hom X A → C.Hom X B → C.Hom X (.conj A B)
  pair_fst : ∀ {X A B} (f : C.Hom X A) (g : C.Hom X B), C.comp (pair f g) (fst A B) = f
  pair_snd : ∀ {X A B} (f : C.Hom X A) (g : C.Hom X B), C.comp (pair f g) (snd A B) = g
  pair_eta : ∀ {X A B} (f : C.Hom X (.conj A B)),
    pair (C.comp f (fst A B)) (C.comp f (snd A B)) = f
  inl : (A B : Formula P) → C.Hom A (.disj A B)
  inr : (A B : Formula P) → C.Hom B (.disj A B)
  copair : {A B X : Formula P} → C.Hom A X → C.Hom B X → C.Hom (.disj A B) X
  inl_copair : ∀ {A B X} (f : C.Hom A X) (g : C.Hom B X),
    C.comp (inl A B) (copair f g) = f
  inr_copair : ∀ {A B X} (f : C.Hom A X) (g : C.Hom B X),
    C.comp (inr A B) (copair f g) = g
  copair_eta : ∀ {A B X} (f : C.Hom (.disj A B) X),
    copair (C.comp (inl A B) f) (C.comp (inr A B) f) = f
  toTop : (A : Formula P) → C.Hom A .top
  toTop_unique : ∀ {A} (f : C.Hom A .top), f = toTop A
  fromBot : (A : Formula P) → C.Hom .bot A
  fromBot_unique : ∀ {A} (f : C.Hom .bot A), f = fromBot A
  dist : (A B D : Formula P) → C.Hom (.conj A (.disj B D)) (.disj (.conj A B) D)

namespace Structure

variable {P : Type u} {C : Category.{u,v} (Formula P)} (S : Structure C)

def prodMap {A B D E : Formula P} (f : C.Hom A D) (g : C.Hom B E) :
    C.Hom (.conj A B) (.conj D E) :=
  S.pair (C.comp (S.fst A B) f) (C.comp (S.snd A B) g)

def sumMap {A B D E : Formula P} (f : C.Hom A D) (g : C.Hom B E) :
    C.Hom (.disj A B) (.disj D E) :=
  S.copair (C.comp f (S.inl D E)) (C.comp g (S.inr D E))

def swap (A : Formula P) : C.Hom (.conj A A) (.conj A A) :=
  S.pair (S.snd A A) (S.fst A A)

def j (A : Formula P) : C.Hom A (.disj A .top) := S.inl A .top

def u (A B : Formula P) : C.Hom (.conj A A) (.disj (.conj A B) A) :=
  C.comp (S.prodMap (C.id A) (S.inr B A)) (S.dist A B A)

def fold (A B : Formula P) : C.Hom (.conj A A) A :=
  C.comp (S.u A B) (S.copair (S.fst A B) (C.id A))

theorem pair_ext {X A B : Formula P} {f g : C.Hom X (.conj A B)}
    (h₁ : C.comp f (S.fst A B) = C.comp g (S.fst A B))
    (h₂ : C.comp f (S.snd A B) = C.comp g (S.snd A B)) : f = g := by
  rw [← S.pair_eta f, h₁, h₂, S.pair_eta]

theorem copair_ext {A B X : Formula P} {f g : C.Hom (.disj A B) X}
    (h₁ : C.comp (S.inl A B) f = C.comp (S.inl A B) g)
    (h₂ : C.comp (S.inr A B) f = C.comp (S.inr A B) g) : f = g := by
  rw [← S.copair_eta f, h₁, h₂, S.copair_eta]

theorem comp_pair {X Y A B : Formula P} (k : C.Hom X Y) (f : C.Hom Y A) (g : C.Hom Y B) :
    C.comp k (S.pair f g) = S.pair (C.comp k f) (C.comp k g) := by
  apply S.pair_ext <;> rw [C.assoc]
  · rw [S.pair_fst, S.pair_fst]
  · rw [S.pair_snd, S.pair_snd]

theorem copair_comp {A B X Y : Formula P} (f : C.Hom A X) (g : C.Hom B X) (k : C.Hom X Y) :
    C.comp (S.copair f g) k = S.copair (C.comp f k) (C.comp g k) := by
  apply S.copair_ext <;> rw [← C.assoc]
  · rw [S.inl_copair, S.inl_copair]
  · rw [S.inr_copair, S.inr_copair]

theorem prodMap_comp {A B D E F H : Formula P}
    (f : C.Hom A D) (g : C.Hom B E) (k : C.Hom D F) (l : C.Hom E H) :
    C.comp (S.prodMap f g) (S.prodMap k l) = S.prodMap (C.comp f k) (C.comp g l) := by
  unfold prodMap
  rw [S.comp_pair]
  simp only [← C.assoc, S.pair_fst, S.pair_snd]

end Structure

/-- A congruence on existing hom-sets, compatible with the operations used in §5. -/
structure Congruence {P : Type u} {C : Category.{u,v} (Formula P)} (S : Structure C) where
  Rel : {A B : Formula P} → C.Hom A B → C.Hom A B → Prop
  refl : ∀ {A B} (f : C.Hom A B), Rel f f
  symm : ∀ {A B} {f g : C.Hom A B}, Rel f g → Rel g f
  trans : ∀ {A B} {f g h : C.Hom A B}, Rel f g → Rel g h → Rel f h
  comp : ∀ {A B D} {f f' : C.Hom A B} {g g' : C.Hom B D},
    Rel f f' → Rel g g' → Rel (C.comp f g) (C.comp f' g')
  pair : ∀ {X A B} {f f' : C.Hom X A} {g g' : C.Hom X B},
    Rel f f' → Rel g g' → Rel (S.pair f g) (S.pair f' g')
  copair : ∀ {A B X} {f f' : C.Hom A X} {g g' : C.Hom B X},
    Rel f f' → Rel g g' → Rel (S.copair f g) (S.copair f' g')

namespace Congruence

variable {P : Type u} {C : Category.{u,v} (Formula P)} {S : Structure C} (Q : Congruence S)

theorem of_eq {A B : Formula P} {f g : C.Hom A B} (h : f = g) : Q.Rel f g :=
  h ▸ Q.refl f

theorem pre {X A B : Formula P} (k : C.Hom X A) {f g : C.Hom A B} (h : Q.Rel f g) :
    Q.Rel (C.comp k f) (C.comp k g) := Q.comp (Q.refl k) h

theorem post {A B D : Formula P} {f g : C.Hom A B} (h : Q.Rel f g) (k : C.Hom B D) :
    Q.Rel (C.comp f k) (C.comp g k) := Q.comp h (Q.refl k)

theorem copair_ext {A B X : Formula P} {f g : C.Hom (.disj A B) X}
    (h₁ : Q.Rel (C.comp (S.inl A B) f) (C.comp (S.inl A B) g))
    (h₂ : Q.Rel (C.comp (S.inr A B) f) (C.comp (S.inr A B) g)) : Q.Rel f g := by
  have h := Q.copair h₁ h₂
  rw [S.copair_eta, S.copair_eta] at h
  exact h

theorem prodMap {A B D E : Formula P} {f f' : C.Hom A D} {g g' : C.Hom B E}
    (hf : Q.Rel f f') (hg : Q.Rel g g') : Q.Rel (S.prodMap f g) (S.prodMap f' g') :=
  Q.pair (Q.pre _ hf) (Q.pre _ hg)

/-- Totality quantifies only over arrows already in each hom-set. -/
def Total : Prop := ∀ {A B : Formula P} (f g : C.Hom A B), Q.Rel f g

end Congruence

/-- A faithful interpretation of the original category in tagged occurrence relations.
The product/coproduct relation laws describe operations, not quotient faithfulness. -/
structure OccurrenceInterpretation {P : Type u} {C : Category.{u,v} (Formula P)}
    (S : Structure C) (Z : ZeroIdentity C) where
  map : {A B : Formula P} → C.Hom A B → Relations.Rel A.Occ B.Occ
  faithful : ∀ {A B} {f g : C.Hom A B}, map f = map g → f = g
  map_id : ∀ A, map (C.id A) = Relations.graph id
  map_comp : ∀ {A B D} (f : C.Hom A B) (g : C.Hom B D),
    map (C.comp f g) = Relations.comp (map f) (map g)
  map_fst : ∀ A B, map (S.fst A B) = Relations.fstRel
  map_snd : ∀ A B, map (S.snd A B) = Relations.sndRel
  map_pair : ∀ {X A B} (f : C.Hom X A) (g : C.Hom X B),
    map (S.pair f g) = Relations.pair (map f) (map g)
  map_inl : ∀ A B, map (S.inl A B) = Relations.graph Sum.inl
  map_inr : ∀ A B, map (S.inr A B) = Relations.graph Sum.inr
  map_copair : ∀ {A B X} (f : C.Hom A X) (g : C.Hom B X),
    map (S.copair f g) = Relations.copair (map f) (map g)
  map_zero : ∀ A, map (Z.zero A) = Relations.empty
  map_dist : ∀ A B D, map (S.dist A B D) = Relations.graph Relations.reassoc

end DosenPetric
