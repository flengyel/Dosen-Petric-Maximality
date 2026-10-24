module

public import DosenPetric.GentzenSharedContractionRanks

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.W3.SharedContraction
universe u
variable {P : Type u}

theorem fusion_left (C : NormalForm P) (gs hs : List (List (NormalForm P)))
    (Θ Λ Δ : List (NormalForm P)) (hI : repeated C hs++Λ = gaps gs++C::Θ)
    (hn : 2 ≤ gs.length) (hm : 2 ≤ hs.length)
    (h : At.shift (gaps gs) (.here C Θ) ∈ (selectedCopies C hs Λ).map (At.cast hI))
    (f : G P (repeated C gs++Θ) Δ) :
    ofTerm (flatL ⟨C,gs,hs,Θ,Λ,hI⟩ hn hm h Δ f).denote =
      ofTerm (oldL ⟨C,gs,hs,Θ,Λ,hI⟩ hn hm Δ f).denote :=
  denoteL ⟨C,gs,hs,Θ,Λ,hI⟩ hn hm h Δ f

theorem fusion_right (C : NormalForm P) (gs hs : List (List (NormalForm P)))
    (Θ Λ Γ : List (NormalForm P)) (hI : repeated C hs++Λ = gaps gs++C::Θ)
    (hn : 2 ≤ gs.length) (hm : 2 ≤ hs.length)
    (h : At.shift (gaps gs) (.here C Θ) ∈ (selectedCopies C hs Λ).map (At.cast hI))
    (f : G P Γ (repeated C gs++Θ)) :
    ofTerm (flatR ⟨C,gs,hs,Θ,Λ,hI⟩ hn hm h Γ f).denote =
      ofTerm (oldR ⟨C,gs,hs,Θ,Λ,hI⟩ hn hm Γ f).denote :=
  denoteR ⟨C,gs,hs,Θ,Λ,hI⟩ hn hm h Γ f

end DosenPetric.Reduced.Gentzen.W3.SharedContraction
