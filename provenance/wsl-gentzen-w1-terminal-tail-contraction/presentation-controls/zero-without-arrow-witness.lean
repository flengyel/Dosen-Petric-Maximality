module
import DosenPetric
open DosenPetric DosenPetric.Presentation
example : Hom (P := Unit) .top .bot := (zeroIdentity Unit).zeroOf ((category Unit).id .top)
