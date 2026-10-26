module

import DosenPetric

set_option autoImplicit false
universe u
open DosenPetric DosenPetric.Reduced DosenPetric.Reduced.Gentzen

example {P : Type u} {C : NormalForm P} {Φ Ξ Ω Ψ U V : List (NormalForm P)}
    (f : G P Φ (C::Ξ)) (g : G P (C::Ω) Ψ) (w : G P U V) (x : At U C) :
    ReducesL f g w x := reducibility_left f g w x

example {P : Type u} {C : NormalForm P} {Φ Ξ Ω Ψ U V : List (NormalForm P)}
    (f : G P Φ (C::Ξ)) (g : G P (C::Ω) Ψ) (w : G P U V) (x : At V C) :
    ReducesR f g w x := reducibility_right f g w x

#check DosenPetric.Reduced.Gentzen.reducibility_left
#check DosenPetric.Reduced.Gentzen.reducibility_right
#check DosenPetric.Reduced.Gentzen.AllInputReducer.left
#check DosenPetric.Reduced.Gentzen.AllInputReducer.right
#check DosenPetric.Reduced.Gentzen.UnrestrictedExchange.left
#check DosenPetric.Reduced.Gentzen.UnrestrictedExchange.right
#check DosenPetric.Reduced.Gentzen.W6.TerminalOne.reducesFirst
#check DosenPetric.Reduced.Gentzen.W6.TerminalOne.reducesSecond
#check DosenPetric.Reduced.Gentzen.ProofAddress.outside_of_incomparable
#check DosenPetric.Reduced.Gentzen.ProofAddress.outside_cluster
#print DosenPetric.Reduced.Gentzen.reducibility_left
#print DosenPetric.Reduced.Gentzen.reducibility_right
