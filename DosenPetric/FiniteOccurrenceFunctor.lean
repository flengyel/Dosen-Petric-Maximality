module

public import DosenPetric.FormulaFiniteOccurrences
public import DosenPetric.PresentationSubstitutionOperations

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric

/-- A finite set with an explicit ordinal-coordinate bijection. -/
structure FiniteSet where
  carrier : Type
  size : Nat
  encode : carrier → Fin size
  decode : Fin size → carrier
  decode_encode : ∀ x, decode (encode x) = x
  encode_decode : ∀ i, encode (decode i) = i

namespace FiniteSet

def relationCategory : Category FiniteSet where
  Hom A B := Relations.Rel A.carrier B.carrier
  id _ := Relations.graph _root_.id
  comp := Relations.comp
  id_comp := Relations.id_comp
  comp_id := Relations.comp_id
  assoc := Relations.comp_assoc

end FiniteSet
namespace Presentation
universe u
variable {P : Type u}

def occurrenceFiniteSet (A : Formula P) : FiniteSet where
  carrier := A.Occ
  size := A.occurrenceCount
  encode := A.occurrenceIndex
  decode := A.occurrenceAt
  decode_encode := A.occurrenceAt_index
  encode_decode := A.occurrenceIndex_at

/-- The actual functor G into finite sets and relations, with explicit finite
coordinates for every object, including formulas with no occurrences. -/
def finiteOccurrenceFunctor (P : Type u) : Functor (category P) FiniteSet.relationCategory where
  obj := occurrenceFiniteSet
  map := occurrenceMap
  map_id := occurrence_id
  map_comp := occurrence_comp

theorem finiteOccurrenceFunctor_faithful {A B : Formula P} {f g : Hom A B}
    (h : (finiteOccurrenceFunctor P).map f = (finiteOccurrenceFunctor P).map g) : f = g := coherence h

end Presentation
end DosenPetric
