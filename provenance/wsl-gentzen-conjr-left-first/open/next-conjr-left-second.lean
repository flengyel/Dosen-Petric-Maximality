module
import DosenPetric.GentzenConjLeftSelected
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open DosenPetric DosenPetric.Reduced DosenPetric.Reduced.Gentzen
namespace NextLeftSecond
variable {P : Type u}
def reconstruct {Γ Θ Δ E T J : List (NormalForm P)} {A B : NormalForm P}
    (f : G P Γ (A :: Δ)) (k : G P (T ++ Θ) (J ++ (B :: E))) :
    G P (T ++ (Γ ++ Θ)) (J ++ (.conj A B :: (Δ ++ E))) :=
  (HeadRouting.front J (Δ ++ E) (.conj A B)).inverse.right
    (((BinaryMix.swapBlocks Δ J E).consFixed (.conj A B)).right
      ((BinaryMix.swapBlocks Γ T Θ).left
        (G.conjR f ((HeadRouting.front J E B).right k))))
example {Γ Θ Δ E T J : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P Γ (A :: Δ)) (g : G P Θ (B :: C :: E)) (h : G P (C :: T) J) :
    ofTerm (G.cut ((HeadRouting.front (.conj A B :: Δ) E C).right
      (G.conjR (Δ := Δ) (Λ := C :: E) f g)) h).denote =
      ofTerm (reconstruct f (G.cut ((HeadRouting.front [B] E C).right g) h)).denote := by
  rw [cut_splice,ExchangeScript.right_denote,G.denote_conjR]
end NextLeftSecond
