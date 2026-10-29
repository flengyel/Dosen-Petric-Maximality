module
import DosenPetric
open DosenPetric DosenPetric.Reduced DosenPetric.Reduced.Gentzen
example {P : Type} (Q : Congruence (Presentation.operations P))
    (A : Formula P) (h : ContextualCollapse.K Q (Z := Presentation.zeroIdentity P) A) : Q.Total :=
  Presentation.ShortProof.total Q h
