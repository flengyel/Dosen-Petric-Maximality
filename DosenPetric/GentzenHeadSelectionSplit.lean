module

public import DosenPetric.GentzenRetainedOnly

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.ContractionSelection
universe u
variable {P : Type u}

/-- Joint extraction at a binary logical conclusion. The principal formula is
an index; selection of it forces its type to be the contracted formula. -/
inductive HeadSplit (C : NormalForm P) (F U : List (NormalForm P)) :
    {D : NormalForm P}→{K : List (NormalForm P)}→ContractionSelection C (D::(F++U)) K→Type u where
  | onlyFresh : HeadSplit C F U (.last (F++U))
  | parametricLeft {K} (D : NormalForm P) (p : ContractionSelection C F K) :
      HeadSplit C F U (.fixed D (p.extend U))
  | parametricRight {L} (D : NormalForm P) (q : ContractionSelection C U L) :
      HeadSplit C F U (.fixed D (q.prependFixed F))
  | parametricBoth {K L} (D : NormalForm P) (p : ContractionSelection C F K) (q : ContractionSelection C U L) :
      HeadSplit C F U (.fixed D (p.chain q))
  | selectedLeft {K} (p : ContractionSelection C F K) : HeadSplit C F U (.more (p.extend U))
  | selectedRight {L} (q : ContractionSelection C U L) : HeadSplit C F U (.more (q.prependFixed F))
  | selectedBoth {K L} (p : ContractionSelection C F K) (q : ContractionSelection C U L) :
      HeadSplit C F U (.more (p.chain q))

theorem head_split_exists {C D : NormalForm P} (F U : List (NormalForm P)) {K : List (NormalForm P)}
    (p : ContractionSelection C (D::(F++U)) K) : Nonempty (HeadSplit C F U p) := by
  cases p with
  | last => exact ⟨.onlyFresh⟩
  | fixed D p =>
    obtain ⟨h⟩:=split_exists F U p
    cases h with
    | left p => exact ⟨.parametricLeft D p⟩
    | right q => exact ⟨.parametricRight D q⟩
    | both p q => exact ⟨.parametricBoth D p q⟩
  | more p =>
    obtain ⟨h⟩:=split_exists F U p
    cases h with
    | left p => exact ⟨.selectedLeft p⟩
    | right q => exact ⟨.selectedRight q⟩
    | both p q => exact ⟨.selectedBoth p q⟩

end DosenPetric.Reduced.Gentzen.ContractionSelection
