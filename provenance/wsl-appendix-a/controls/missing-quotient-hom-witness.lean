module
import DosenPetric
open DosenPetric DosenPetric.Reduced DosenPetric.Reduced.Gentzen
example (Q : Presentation.ProofCongruence Nat) : Q.fragment.QuotientHom .top .bot := Q.fragment.classOf (Presentation.id .top)
