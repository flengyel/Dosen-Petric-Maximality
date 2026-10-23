module

public import DosenPetric.GentzenMixedThinning

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

namespace Iso

def cast {A B A' B' : NormalForm P} (hA : A = A') (hB : B = B') (i : Iso A B) : Iso A' B' :=
  hA ▸ hB ▸ i

theorem cast_heq {A B A' B' : NormalForm P} (hA : A = A') (hB : B = B') (i : Iso A B) :
    (i.cast hA hB) ≍ i := by cases hA; cases hB; rfl

theorem cast_tensor (o : Op) (X : NormalForm P) {A B A' B' : NormalForm P}
    (hA : A = A') (hB : B = B') (i : Iso A B) :
    (Iso.tensor o (Iso.refl X) i).cast (congrArg (o.formula X) hA) (congrArg (o.formula X) hB) =
      Iso.tensor o (Iso.refl X) (i.cast hA hB) := by
  cases hA; cases hB; rfl
end Iso

def exchangeCore (o : Op) (X Y Δ : List (NormalForm P)) :
    Iso (fold o (X ++ Y ++ Δ)) (fold o (Y ++ X ++ Δ)) :=
  ((append o (X ++ Y) Δ).symm).trans
    ((Iso.tensor o ((append o X Y).symm.trans
      ((Iso.swap o (fold o X) (fold o Y)).trans (append o Y X)))
      (Iso.refl (fold o Δ))).trans (append o (Y ++ X) Δ))

theorem prefix_fold (o : Op) (Γ Z : List (NormalForm P)) :
    fold o (Γ ++ Z) = Γ.foldr o.formula (fold o Z) := by
  induction Γ with
  | nil => rfl
  | cons A Γ ih => exact congrArg (o.formula A) ih

theorem exchange_prefix (o : Op) (Γ X Y Δ : List (NormalForm P)) :
    fold o (Γ ++ X ++ Y ++ Δ) = Γ.foldr o.formula (fold o (X ++ Y ++ Δ)) := by
  simpa only [List.append_assoc] using prefix_fold o Γ (X ++ Y ++ Δ)

theorem exchange_cast (o : Op) (Γ X Y Δ : List (NormalForm P)) :
    exchange o Γ X Y Δ =
      (under o Γ (exchangeCore o X Y Δ)).cast
        (exchange_prefix o Γ X Y Δ).symm (exchange_prefix o Γ Y X Δ).symm := by
  unfold exchange
  apply eq_of_heq
  change (cast _ (cast _ (under o Γ (exchangeCore o X Y Δ)))) ≍ _
  exact ((cast_heq _ _).trans (cast_heq _ _)).trans (Iso.cast_heq ..).symm

theorem exchange_nil (o : Op) (X Y Δ : List (NormalForm P)) :
    exchange o [] X Y Δ = exchangeCore o X Y Δ := by
  rw [exchange_cast]
  rfl

theorem exchange_cons (o : Op) (A : NormalForm P) (Γ X Y Δ : List (NormalForm P)) :
    exchange o (A :: Γ) X Y Δ = Iso.tensor o (Iso.refl A) (exchange o Γ X Y Δ) := by
  rw [exchange_cast, exchange_cast]
  exact Iso.cast_tensor o A (exchange_prefix o Γ X Y Δ).symm
    (exchange_prefix o Γ Y X Δ).symm (under o Γ (exchangeCore o X Y Δ))

end DosenPetric.Reduced.Gentzen
