module
import DosenPetric
open DosenPetric DosenPetric.Reduced DosenPetric.Reduced.Gentzen
example (l : Literal Nat) :
    occurrenceMap (PureEdge.arrow (P:=Nat) (A:=.lit l) (B:=.disj (.lit l) (.lit l))
      ⟨l,.here l,.left (.lit l) (.here l)⟩) l.point (Sum.inr l.point) := by
  rw [PureEdge.relation]
  constructor <;> rfl
