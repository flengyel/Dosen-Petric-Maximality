module

public import DosenPetric.AtomicExtraction

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced
universe u
variable {P : Type u}
theorem ofTerm_id (A : NormalForm P) : ofTerm (.id A) = id A := rfl

theorem ofTerm_comp {A B C : NormalForm P} (f : Term P A B) (g : Term P B C) :
    ofTerm (.comp f g) = comp (ofTerm f) (ofTerm g) := rfl

theorem ofTerm_tensor (o : Op) {A B C D : NormalForm P} (f : Term P A C) (g : Term P B D) :
    ofTerm (.tensor o f g) = tensor o (ofTerm f) (ofTerm g) := rfl

namespace AtomicPorts

@[reducible] def block : Op → P → NormalForm P
  | .conj, p => Atomic.etaObject p
  | .disj, p => Atomic.epsilonObject p

/-- Left-associated source port objects, in occurrence-list order. -/
@[reducible] def expand (o : Op) (A : NormalForm P) : List P → NormalForm P
  | [] => A
  | p :: ps => expand o (o.formula A (block o p)) ps

def mapTerm (o : Op) (w : (p : P) → Term P (block o p) (block o p))
    {A B : NormalForm P} (f : Term P A B) : (ps : List P) → Term P (expand o A ps) (expand o B ps)
  | [] => f
  | p :: ps => mapTerm o w (.tensor o f (w p)) ps

def map (o : Op) (w : (p : P) → Hom (block o p) (block o p))
    {A B : NormalForm P} (f : Hom A B) : (ps : List P) → Hom (expand o A ps) (expand o B ps)
  | [] => f
  | p :: ps => map o w (tensor o f (w p)) ps

theorem map_ofTerm (o : Op) (w : (p : P) → Term P (block o p) (block o p))
    {A B : NormalForm P} (f : Term P A B) (ps : List P) :
    map o (fun p => ofTerm (w p)) (ofTerm f) ps = ofTerm (mapTerm o w f ps) := by
  induction ps generalizing A B with
  | nil => rfl
  | cons p ps ih => exact ih (.tensor o f (w p))

def lift {A B : NormalForm P} (o : Op) (f : Term P A B) (ps : List P) :=
  mapTerm o (fun p => .id (block o p)) f ps

def zeros {A B : NormalForm P} (o : Op) (f : Term P A B) (ps : List P) :=
  mapTerm o (fun p => .zero (block o p)) f ps

def mask (o : Op) (A : NormalForm P) (ps : List P) := zeros o (.id A) ps

theorem mapTerm_positive (o : Op) (w : (p : P) → Term P (block o p) (block o p))
    (hw : ∀ p, (w p).Positive) {A B : NormalForm P} (f : Term P A B) (hf : f.Positive) (ps : List P) :
    (mapTerm o w f ps).Positive := by
  induction ps generalizing A B with
  | nil => exact hf
  | cons p ps ih => exact ih (.tensor o f (w p)) (.tensor o hf (hw p))

theorem lift_positive {A B : NormalForm P} (o : Op) (f : Term P A B) (hf : f.Positive) (ps : List P) :
    (lift o f ps).Positive := mapTerm_positive o _ (fun _ => .id _) f hf ps

theorem zeros_positive {A B : NormalForm P} (o : Op) (f : Term P A B) (hf : f.Positive) (ps : List P) :
    (zeros o f ps).Positive := mapTerm_positive o _ (fun _ => .zero _) f hf ps

def etaOne (A : NormalForm P) (p : P) : Term P A (.conj A (Atomic.etaObject p)) :=
  .comp (.rightIn .conj A) (.tensor .conj (.id A) (.eta p))

def epsilonOne (A : NormalForm P) (p : P) : Term P (.disj A (Atomic.epsilonObject p)) A :=
  .comp (.tensor .disj (.id A) (.epsilon p)) (.rightOut .disj A)

def etaPrefix (A : NormalForm P) : (ps : List P) → Term P A (expand .conj A ps)
  | [] => .id A
  | p :: ps => .comp (etaOne A p) (etaPrefix (.conj A (Atomic.etaObject p)) ps)

def epsilonSuffix (A : NormalForm P) : (ps : List P) → Term P (expand .disj A ps) A
  | [] => .id A
  | p :: ps => .comp (epsilonSuffix (.disj A (Atomic.epsilonObject p)) ps) (epsilonOne A p)

theorem etaOne_nat {A B : NormalForm P} (f : Hom A B) (p : P)
    (w : Hom (Atomic.etaObject p) (Atomic.etaObject p)) :
    comp (ofTerm (etaOne A p)) (tensor .conj f w) = comp f (ofTerm (etaOne B p)) := by
  change comp (comp (rightIn .conj A) (tensor .conj (id A) (ofTerm (.eta p)))) _ = _
  have hw : comp (ofTerm (.eta p)) w = ofTerm (.eta p) := fromTop_unique _ _
  rw [Laws.assoc, Laws.tensor_comp, Laws.id_comp, hw]
  have ht : tensor .conj f (ofTerm (.eta p)) =
      comp (tensor .conj f (id .top)) (tensor .conj (id B) (ofTerm (.eta p))) := by
    rw [Laws.tensor_comp, Laws.comp_id, Laws.id_comp]
  rw [ht, ← Laws.assoc, Laws.rightIn_nat, Laws.assoc]
  rfl

theorem epsilonOne_nat {A B : NormalForm P} (f : Hom A B) (p : P)
    (w : Hom (Atomic.epsilonObject p) (Atomic.epsilonObject p)) :
    comp (tensor .disj f w) (ofTerm (epsilonOne B p)) = comp (ofTerm (epsilonOne A p)) f := by
  change comp _ (comp (tensor .disj (id B) (ofTerm (.epsilon p))) (rightOut .disj B)) = _
  have hw : comp w (ofTerm (.epsilon p)) = ofTerm (.epsilon p) := toBot_unique _ _
  rw [← Laws.assoc, Laws.tensor_comp, Laws.comp_id, hw]
  have ht : tensor .disj f (ofTerm (.epsilon p)) =
      comp (tensor .disj (id A) (ofTerm (.epsilon p))) (tensor .disj f (id .bot)) := by
    rw [Laws.tensor_comp, Laws.id_comp, Laws.comp_id]
  rw [ht, Laws.assoc, ← Laws.rightOut_nat, ← Laws.assoc]
  rfl

theorem prefix_natural (w : (p : P) → Hom (block .conj p) (block .conj p))
    {A B : NormalForm P} (f : Hom A B) (ps : List P) :
    comp (ofTerm (etaPrefix A ps)) (map .conj w f ps) = comp f (ofTerm (etaPrefix B ps)) := by
  induction ps generalizing A B with
  | nil => exact (Laws.id_comp f).trans (Laws.comp_id f).symm
  | cons p ps ih =>
    change comp (comp (ofTerm (etaOne A p)) (ofTerm (etaPrefix _ ps))) (map .conj w (tensor .conj f (w p)) ps) = _
    rw [Laws.assoc, ih, ← Laws.assoc, etaOne_nat, Laws.assoc]
    rfl

theorem suffix_natural (w : (p : P) → Hom (block .disj p) (block .disj p))
    {A B : NormalForm P} (f : Hom A B) (ps : List P) :
    comp (map .disj w f ps) (ofTerm (epsilonSuffix B ps)) = comp (ofTerm (epsilonSuffix A ps)) f := by
  induction ps generalizing A B with
  | nil => exact (Laws.comp_id f).trans (Laws.id_comp f).symm
  | cons p ps ih =>
    change comp (map .disj w (tensor .disj f (w p)) ps)
      (comp (ofTerm (epsilonSuffix _ ps)) (ofTerm (epsilonOne B p))) = _
    rw [← Laws.assoc, ih, Laws.assoc, epsilonOne_nat, ← Laws.assoc]
    rfl

theorem prefix_mask (A : NormalForm P) (ps : List P) :
    comp (ofTerm (etaPrefix A ps)) (ofTerm (mask .conj A ps)) = ofTerm (etaPrefix A ps) := by
  have h := prefix_natural (fun p => ofTerm (.zero (block .conj p))) (ofTerm (.id A)) ps
  rw [map_ofTerm, ofTerm_id, Laws.id_comp] at h
  exact h

theorem mask_suffix (A : NormalForm P) (ps : List P) :
    comp (ofTerm (mask .disj A ps)) (ofTerm (epsilonSuffix A ps)) = ofTerm (epsilonSuffix A ps) := by
  have h := suffix_natural (fun p => ofTerm (.zero (block .disj p))) (ofTerm (.id A)) ps
  rw [map_ofTerm, ofTerm_id, Laws.comp_id] at h
  exact h

end AtomicPorts
end DosenPetric.Reduced
