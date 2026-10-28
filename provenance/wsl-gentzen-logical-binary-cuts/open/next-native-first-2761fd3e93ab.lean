module
import DosenPetric.GentzenMixedDisjSymmetry
set_option autoImplicit false
universe u
open DosenPetric DosenPetric.Reduced DosenPetric.Reduced.Gentzen
namespace NextNative
variable {P : Type u}
def firstNative {Γ Θ Δ Λ I D : List (NormalForm P)} {A B : NormalForm P}
    (k : G P (Γ ++ I) (A :: (Δ ++ D))) (g : G P Θ (B :: Λ)) :
    G P ((Γ ++ Θ) ++ I) ((.conj A B :: (Δ ++ Λ)) ++ D) :=
  ((ExchangeScript.exchange (.conj A B :: Δ) D Λ []).reindex
    (by simp only [List.append_nil,List.cons_append,List.append_assoc])
    (by simp only [List.append_nil,List.cons_append,List.append_assoc])).right
      (((ExchangeScript.exchange Γ Θ I []).reindex
        (by simp only [List.append_nil,List.append_assoc])
        (by simp only [List.append_nil,List.append_assoc])).left (G.conjR k g))
example {Γ Θ Δ Λ I D : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P (C :: Γ) (A :: Δ)) (g : G P Θ (B :: Λ)) (h : G P I (C :: D)) :
    ofTerm (G.cut h (G.conjR f g)).denote =
      ofTerm (firstNative (G.cut h f) g).denote := by
  rw [cut_splice,G.denote_conjR]
end NextNative
