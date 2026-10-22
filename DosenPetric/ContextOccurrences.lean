module

public import DosenPetric.ContextualMaps

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced
universe u
variable {P : Type u}
open Relations

namespace Op

def join (o : Op) (A B : NormalForm P) :
    Sum A.formula.Occ B.formula.Occ → (o.formula A B).formula.Occ :=
  match o with | .conj => _root_.id | .disj => _root_.id

def split (o : Op) (A B : NormalForm P) :
    (o.formula A B).formula.Occ → Sum A.formula.Occ B.formula.Occ :=
  match o with | .conj => _root_.id | .disj => _root_.id

end Op

namespace Context

/-- Tags in surrounding formulas; this type does not depend on the inserted formula. -/
def Fixed : Context P → Type
  | .hole => Empty
  | .left _ C K => Sum C.formula.Occ K.Fixed
  | .right _ K C => Sum K.Fixed C.formula.Occ

/-- Fixed occurrences and occurrences contributed by the distinguished hole. -/
def encode : (K : Context P) → (A : NormalForm P) →
    Sum K.Fixed A.formula.Occ → (K.plug A).formula.Occ
  | .hole, _, .inl z => nomatch z
  | .hole, _, .inr x => x
  | .left o C K, A, .inl (.inl c) => o.join C (K.plug A) (.inl c)
  | .left o C K, A, .inl (.inr z) => o.join C (K.plug A) (.inr (K.encode A (.inl z)))
  | .left o C K, A, .inr x => o.join C (K.plug A) (.inr (K.encode A (.inr x)))
  | .right o K C, A, .inl (.inl z) => o.join (K.plug A) C (.inl (K.encode A (.inl z)))
  | .right o K C, A, .inl (.inr c) => o.join (K.plug A) C (.inr c)
  | .right o K C, A, .inr x => o.join (K.plug A) C (.inl (K.encode A (.inr x)))

def decode : (K : Context P) → (A : NormalForm P) →
    (K.plug A).formula.Occ → Sum K.Fixed A.formula.Occ
  | .hole, _, x => .inr x
  | .left o C K, A, x => match o.split C (K.plug A) x with
    | .inl c => .inl (.inl c)
    | .inr z => match K.decode A z with
      | .inl z => .inl (.inr z)
      | .inr x => .inr x
  | .right o K C, A, x => match o.split (K.plug A) C x with
    | .inr c => .inl (.inr c)
    | .inl z => match K.decode A z with
      | .inl z => .inl (.inl z)
      | .inr x => .inr x

theorem decode_encode (K : Context P) (A : NormalForm P) (x : Sum K.Fixed A.formula.Occ) :
    K.decode A (K.encode A x) = x := by
  induction K with
  | hole => cases x with | inl z => exact nomatch z | inr x => rfl
  | left o C K ih =>
    cases o <;> cases x with
    | inl x => cases x <;> simp [encode, decode, Op.join, Op.split, ih]
    | inr x => simp [encode, decode, Op.join, Op.split, ih]
  | right o K C ih =>
    cases o <;> cases x with
    | inl x => cases x <;> simp [encode, decode, Op.join, Op.split, ih]
    | inr x => simp [encode, decode, Op.join, Op.split, ih]

theorem encode_decode (K : Context P) (A : NormalForm P) (x : (K.plug A).formula.Occ) :
    K.encode A (K.decode A x) = x := by
  induction K with
  | hole => rfl
  | left o C K ih =>
    cases o <;> cases x with
    | inl c => rfl
    | inr z =>
      have h := ih z
      cases hd : K.decode A z <;> simp_all [encode, decode, Op.join, Op.split]
  | right o K C ih =>
    cases o <;> cases x with
    | inr c => rfl
    | inl z =>
      have h := ih z
      cases hd : K.decode A z <;> simp_all [encode, decode, Op.join, Op.split]

def fixedEmbedding (K : Context P) (A : NormalForm P) (x : K.Fixed) : (K.plug A).formula.Occ :=
  K.encode A (.inl x)

def holeEmbedding (K : Context P) (A : NormalForm P) (x : A.formula.Occ) : (K.plug A).formula.Occ :=
  K.encode A (.inr x)

theorem encode_injective (K : Context P) (A : NormalForm P) {x y : Sum K.Fixed A.formula.Occ}
    (h : K.encode A x = K.encode A y) : x = y := by
  have hh := congrArg (K.decode A) h
  simpa only [decode_encode] using hh

theorem fixedEmbedding_injective (K : Context P) (A : NormalForm P) {x y : K.Fixed}
    (h : K.fixedEmbedding A x = K.fixedEmbedding A y) : x = y := by
  have hh := K.encode_injective A h
  cases hh
  rfl

theorem holeEmbedding_injective (K : Context P) (A : NormalForm P) {x y : A.formula.Occ}
    (h : K.holeEmbedding A x = K.holeEmbedding A y) : x = y := by
  have hh := K.encode_injective A h
  cases hh
  rfl

theorem embeddings_disjoint (K : Context P) (A : NormalForm P) (x : K.Fixed) (y : A.formula.Occ) :
    K.fixedEmbedding A x ≠ K.holeEmbedding A y := by
  intro h
  have hh := K.encode_injective A h
  cases hh

set_option linter.unusedSimpArgs false in
/-- The action fixes each surrounding tag and acts by the supplied relation in the hole. -/
theorem relation_mapTerm {A B : NormalForm P} (K : Context P) (t : Term P A B)
    (x : Sum K.Fixed A.formula.Occ) (y : Sum K.Fixed B.formula.Occ) :
    (K.mapTerm t).relation (K.encode A x) (K.encode B y) ↔
      sumMap (graph _root_.id) t.relation x y := by
  induction K with
  | hole =>
    cases x with
    | inl z => exact nomatch z
    | inr x => cases y with
      | inl z => exact nomatch z
      | inr y => rfl
  | left o C K ih =>
    cases o <;> cases x with
    | inl x =>
      cases x <;> cases y with
      | inl y => cases y <;> simp [mapTerm, encode, Op.join, _root_.id, Term.relation, sumMap, ih, graph] <;>
          constructor <;> intro h <;> cases h <;> rfl
      | inr y => simp [mapTerm, encode, Op.join, _root_.id, Term.relation, sumMap, ih, graph] <;>
          constructor <;> intro h <;> cases h <;> rfl
    | inr x =>
      cases y with
      | inl y => cases y <;> simp [mapTerm, encode, Op.join, _root_.id, Term.relation, sumMap, ih, graph] <;>
          constructor <;> intro h <;> cases h <;> rfl
      | inr y => simp [mapTerm, encode, Op.join, _root_.id, Term.relation, sumMap, ih, graph] <;>
          constructor <;> intro h <;> cases h <;> rfl
  | right o K C ih =>
    cases o <;> cases x with
    | inl x =>
      cases x <;> cases y with
      | inl y => cases y <;> simp [mapTerm, encode, Op.join, _root_.id, Term.relation, sumMap, ih, graph] <;>
          constructor <;> intro h <;> cases h <;> rfl
      | inr y => simp [mapTerm, encode, Op.join, _root_.id, Term.relation, sumMap, ih, graph] <;>
          constructor <;> intro h <;> cases h <;> rfl
    | inr x =>
      cases y with
      | inl y => cases y <;> simp [mapTerm, encode, Op.join, _root_.id, Term.relation, sumMap, ih, graph] <;>
          constructor <;> intro h <;> cases h <;> rfl
      | inr y => simp [mapTerm, encode, Op.join, _root_.id, Term.relation, sumMap, ih, graph] <;>
          constructor <;> intro h <;> cases h <;> rfl

theorem occurrence_map {A B : NormalForm P} (K : Context P) (f : Hom A B)
    (x : Sum K.Fixed A.formula.Occ) (y : Sum K.Fixed B.formula.Occ) :
    occurrenceMap (K.map f) (K.encode A x) (K.encode B y) ↔
      sumMap (graph _root_.id) (occurrenceMap f) x y := by
  induction f using Quotient.inductionOn with | h f => exact K.relation_mapTerm f x y

theorem occurrence_map_decode {A B : NormalForm P} (K : Context P) (f : Hom A B)
    (x : (K.plug A).formula.Occ) (y : (K.plug B).formula.Occ) :
    occurrenceMap (K.map f) x y ↔
      sumMap (graph _root_.id) (occurrenceMap f) (K.decode A x) (K.decode B y) := by
  simpa only [encode_decode] using K.occurrence_map f (K.decode A x) (K.decode B y)

end Context
theorem occurrence_comp {A B C : NormalForm P} (f : Hom A B) (g : Hom B C) :
    occurrenceMap (comp f g) = Relations.comp (occurrenceMap f) (occurrenceMap g) := by
  induction f using Quotient.inductionOn with | h f =>
  induction g using Quotient.inductionOn with | h g => rfl

namespace Context

theorem top_occ_fixed (K : Context P) (x : (K.plug .top).formula.Occ) :
    ∃ z : K.Fixed, K.fixedEmbedding .top z = x := by
  have h := K.encode_decode .top x
  cases hd : K.decode .top x with
  | inl z => exact ⟨z, by simpa only [hd, fixedEmbedding] using h⟩
  | inr z => exact nomatch z

theorem bot_occ_fixed (K : Context P) (x : (K.plug .bot).formula.Occ) :
    ∃ z : K.Fixed, K.fixedEmbedding .bot z = x := by
  have h := K.encode_decode .bot x
  cases hd : K.decode .bot x with
  | inl z => exact ⟨z, by simpa only [hd, fixedEmbedding] using h⟩
  | inr z => exact nomatch z

end Context

theorem eta_prefix_relation (A : NormalForm P) (p : P) :
    occurrenceMap (comp (rightIn .conj A) (tensor .conj (id A) (ofTerm (.eta p)))) =
      graph Sum.inl := by
  funext x y
  apply propext
  change Relations.comp (graph Sum.inl) (sumMap (graph _root_.id) empty) x y ↔ _
  cases y <;> simp [Relations.comp, graph, sumMap, empty]

theorem epsilon_suffix_relation (A : NormalForm P) (p : P)
    (x : (NormalForm.disj A (.conj (.lit (.pos p)) (.lit (.neg p)))).formula.Occ) (y : A.formula.Occ) :
    occurrenceMap (comp (tensor .disj (id A) (ofTerm (.epsilon p))) (rightOut .disj A)) x y ↔
      x = Sum.inl y := by
  change Relations.comp (sumMap (graph _root_.id) empty) (graph Presentation.Occurrence.dropRight) x y ↔ _
  cases x <;> simp [Relations.comp, graph, sumMap, empty, Sum.exists, Presentation.Occurrence.dropRight]

namespace Context

/-- The source's “same pairs”, p.320, with the missing domain embedding explicit. -/
theorem gEta_comp_relation {A : NormalForm P} (K : Context P) (p : P)
    (f : Hom A (K.plug .top)) (x : A.formula.Occ)
    (y : (K.plug (.disj (.lit (.neg p)) (.lit (.pos p)))).formula.Occ) :
    occurrenceMap (comp f (K.map (ofTerm (.eta p)))) x y ↔
      occurrenceMap (comp (tensor .conj f (zero (.disj (.lit (.neg p)) (.lit (.pos p)))))
        (ofTerm (K.gConj (.disj (.lit (.neg p)) (.lit (.pos p)))))) (.inl x) y := by
  have h := K.gEta_comp (ofTerm (.eta p)) f
  rw [← Laws.assoc] at h
  rw [h, occurrence_comp, eta_prefix_relation]
  simp [Relations.comp, graph]

/-- The analogous “same pairs” comparison with an explicit codomain embedding. -/
theorem gEpsilon_comp_relation {A : NormalForm P} (K : Context P) (p : P)
    (f : Hom (K.plug .bot) A)
    (x : (K.plug (.conj (.lit (.pos p)) (.lit (.neg p)))).formula.Occ) (y : A.formula.Occ) :
    occurrenceMap (comp (K.map (ofTerm (.epsilon p))) f) x y ↔
      occurrenceMap (comp (ofTerm (K.gDisj (.conj (.lit (.pos p)) (.lit (.neg p)))))
        (tensor .disj f (zero (.conj (.lit (.pos p)) (.lit (.neg p)))))) x (.inl y) := by
  have h := K.gEpsilon_comp (ofTerm (.epsilon p)) f
  rw [← Laws.assoc] at h
  rw [h, occurrence_comp]
  change (∃ z, occurrenceMap _ x z ∧ occurrenceMap
    (comp (tensor .disj (id A) (ofTerm (.epsilon p))) (rightOut .disj A)) z y) ↔ _
  simp only [epsilon_suffix_relation]
  simp

end Context

end DosenPetric.Reduced
