module

public import DosenPetric.Collapse

@[expose] public section

set_option autoImplicit false

namespace DosenPetric.GeneratedModel

universe u

/-- Terms of the bicartesian/distributor/zero fragment, with explicit endpoint formulas. -/
inductive Term (P : Type u) : Formula P → Formula P → Type u where
  | id (A) : Term P A A
  | comp {A B D} : Term P A B → Term P B D → Term P A D
  | fst (A B) : Term P (.conj A B) A
  | snd (A B) : Term P (.conj A B) B
  | pair {X A B} : Term P X A → Term P X B → Term P X (.conj A B)
  | inl (A B) : Term P A (.disj A B)
  | inr (A B) : Term P B (.disj A B)
  | copair {A B X} : Term P A X → Term P B X → Term P (.disj A B) X
  | toTop (A) : Term P A .top
  | fromBot (A) : Term P .bot A
  | dist (A B D) : Term P (.conj A (.disj B D)) (.disj (.conj A B) D)
  | zero (A) : Term P A A

namespace Term

variable {P : Type u}

def relation : {A B : Formula P} → Term P A B → Relations.Rel A.Occ B.Occ
  | _, _, .id _ => Relations.graph _root_.id
  | _, _, .comp f g => Relations.comp f.relation g.relation
  | _, _, .fst _ _ => Relations.fstRel
  | _, _, .snd _ _ => Relations.sndRel
  | _, _, .pair f g => Relations.pair f.relation g.relation
  | _, _, .inl _ _ => Relations.graph Sum.inl
  | _, _, .inr _ _ => Relations.graph Sum.inr
  | _, _, .copair f g => Relations.copair f.relation g.relation
  | _, _, .toTop _ => Relations.empty
  | _, _, .fromBot _ => Relations.empty
  | _, _, .dist _ _ _ => Relations.graph Relations.reassoc
  | _, _, .zero _ => Relations.empty

/-- A truth assignment used only to exhibit an empty hom-set of the fragment. -/
def Truth : Formula P → Prop
  | .var _ => True
  | .top => True
  | .bot => False
  | .conj A B => Truth A ∧ Truth B
  | .disj A B => Truth A ∨ Truth B
  | .neg _ => True

theorem preserves_truth {A B : Formula P} (t : Term P A B) : Truth A → Truth B := by
  induction t with
  | id _ => exact _root_.id
  | comp _ _ hf hg => exact fun h => hg (hf h)
  | fst _ _ => exact And.left
  | snd _ _ => exact And.right
  | pair _ _ hf hg => exact fun h => ⟨hf h, hg h⟩
  | inl _ _ => exact Or.inl
  | inr _ _ => exact Or.inr
  | copair _ _ hf hg => exact fun h => h.elim hf hg
  | toTop _ => exact fun _ => True.intro
  | fromBot _ => exact False.elim
  | dist _ _ _ =>
    rintro ⟨ha, hb | hd⟩
    · exact Or.inl ⟨ha, hb⟩
    · exact Or.inr hd
  | zero _ => exact _root_.id

end Term

/-- Only relations denoted by a term of the fragment are arrows of this model. -/
def Hom {P : Type u} (A B : Formula P) :=
  {r : Relations.Rel A.Occ B.Occ // ∃ t : Term P A B, t.relation = r}

def denote {P : Type u} {A B : Formula P} (t : Term P A B) : Hom A B :=
  ⟨t.relation, t, rfl⟩

def compose {P : Type u} {A B D : Formula P} (f : Hom A B) (g : Hom B D) : Hom A D :=
  ⟨Relations.comp f.val g.val, by
    obtain ⟨tf, hf⟩ := f.property
    obtain ⟨tg, hg⟩ := g.property
    exact ⟨.comp tf tg, by dsimp only [Term.relation]; rw [hf, hg]⟩⟩

def pair {P : Type u} {X A B : Formula P} (f : Hom X A) (g : Hom X B) : Hom X (.conj A B) :=
  ⟨Relations.pair f.val g.val, by
    obtain ⟨tf, hf⟩ := f.property
    obtain ⟨tg, hg⟩ := g.property
    exact ⟨.pair tf tg, by dsimp only [Term.relation]; rw [hf, hg]⟩⟩

def copair {P : Type u} {A B X : Formula P} (f : Hom A X) (g : Hom B X) : Hom (.disj A B) X :=
  ⟨Relations.copair f.val g.val, by
    obtain ⟨tf, hf⟩ := f.property
    obtain ⟨tg, hg⟩ := g.property
    exact ⟨.copair tf tg, by dsimp only [Term.relation]; rw [hf, hg]⟩⟩

def category (P : Type u) : Category (Formula P) where
  Hom := Hom
  id A := denote (.id A)
  comp := compose
  id_comp f := Subtype.ext (Relations.id_comp f.val)
  comp_id f := Subtype.ext (Relations.comp_id f.val)
  assoc f g h := Subtype.ext (Relations.comp_assoc f.val g.val h.val)

def operations (P : Type u) : Structure (category P) where
  fst A B := denote (.fst A B)
  snd A B := denote (.snd A B)
  pair := pair
  pair_fst f g := Subtype.ext (Relations.pair_fst f.val g.val)
  pair_snd f g := Subtype.ext (Relations.pair_snd f.val g.val)
  pair_eta f := Subtype.ext (Relations.pair_eta f.val)
  inl A B := denote (.inl A B)
  inr A B := denote (.inr A B)
  copair := copair
  inl_copair f g := Subtype.ext (Relations.inl_copair f.val g.val)
  inr_copair f g := Subtype.ext (Relations.inr_copair f.val g.val)
  copair_eta f := Subtype.ext (Relations.copair_eta f.val)
  toTop A := denote (.toTop A)
  toTop_unique f := by
    apply Subtype.ext
    funext x y
    exact Empty.elim y
  fromBot A := denote (.fromBot A)
  fromBot_unique f := by
    apply Subtype.ext
    funext x y
    exact Empty.elim x
  dist A B D := denote (.dist A B D)

def zero (P : Type u) : ZeroIdentity (category P) where
  zero A := denote (.zero A)
  law f g := Subtype.ext ((Relations.empty_comp f.val).trans (Relations.comp_empty g.val).symm)

/-- The complete interpretation interface is inhabited by the generated fragment model. -/
def interpretation (P : Type u) : OccurrenceInterpretation (operations P) (zero P) where
  map f := f.val
  faithful h := Subtype.ext h
  map_id _ := rfl
  map_comp _ _ := rfl
  map_fst _ _ := rfl
  map_snd _ _ := rfl
  map_pair _ _ := rfl
  map_inl _ _ := rfl
  map_inr _ _ := rfl
  map_copair _ _ := rfl
  map_zero _ := rfl
  map_dist _ _ _ := rfl

theorem nonthin {P : Type u} (p : P) :
    (operations P).fst (.var p) (.var p) ≠ (operations P).snd (.var p) (.var p) := by
  intro h
  exact Relations.projections_distinct (congrArg Subtype.val h)

theorem empty_hom (P : Type u) : ¬ Nonempty ((category P).Hom .top .bot) := by
  rintro ⟨f⟩
  obtain ⟨t, _⟩ := f.property
  exact t.preserves_truth True.intro

end DosenPetric.GeneratedModel
