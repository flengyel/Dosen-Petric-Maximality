module
import DosenPetric.GentzenConjSecondSelected
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open DosenPetric DosenPetric.Reduced DosenPetric.Reduced.Gentzen
namespace NextDisjLeftSecond
variable {P : Type u}
def reconstruct {Γ Θ Δ E T J : List (NormalForm P)} {A B : NormalForm P}
    (f : G P (A :: Γ) Δ) (k : G P (T ++ (B :: Θ)) (J ++ E)) :
    G P (T ++ (.disj A B :: (Γ ++ Θ))) (J ++ (Δ ++ E)) :=
  (BinaryMix.swapBlocks Δ J E).right
    ((HeadRouting.front T (Γ ++ Θ) (.disj A B)).inverse.left
      (((BinaryMix.swapBlocks Γ T Θ).consFixed (.disj A B)).left
        (G.disjL f ((HeadRouting.front T Θ B).left k))))
example {Γ Θ Δ E T J : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P (A :: Γ) Δ) (g : G P (B :: Θ) (C :: E)) (h : G P (C :: T) J) :
    ofTerm (G.cut ((HeadRouting.front Δ E C).right (G.disjL f g)) h).denote =
      ofTerm (reconstruct f (G.cut g h)).denote := by
  rw [cut_splice,ExchangeScript.right_denote,G.denote_disjL]
end NextDisjLeftSecond
