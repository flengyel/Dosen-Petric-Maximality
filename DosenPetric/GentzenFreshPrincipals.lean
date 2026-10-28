module

public import DosenPetric.GentzenLeafShapes
public import DosenPetric.GentzenSelectedRecursion

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

namespace G

theorem conjR_principal_blocked {Γ Θ Δ Λ : List (NormalForm P)} {A B : NormalForm P}
    (f : G P Γ (A :: Δ)) (g : G P Θ (B :: Λ)) :
    AllBlockedAt (conjR f g) .right (.here (.conj A B) (Δ ++ Λ)) :=
  allBlockedAt_of_leaf _ _ _ (by rfl)

theorem disjL_principal_blocked {Γ Θ Δ Λ : List (NormalForm P)} {A B : NormalForm P}
    (f : G P (A :: Γ) Δ) (g : G P (B :: Θ) Λ) :
    AllBlockedAt (disjL f g) .left (.here (.disj A B) (Γ ++ Θ)) :=
  allBlockedAt_of_leaf _ _ _ (by rfl)

theorem conjL_principal_blocked (Γ Θ Δ : List (NormalForm P)) (A B : NormalForm P)
    (f : G P (Γ ++ A :: B :: Θ) Δ) :
    AllBlockedAt (conjL Γ Θ Δ A B f) .left (At.shift Γ (.here (.conj A B) Θ)) :=
  allBlockedAt_of_leaf _ _ _ (conjL_principal_leaf ..)

theorem disjR_principal_blocked (Γ Δ Λ : List (NormalForm P)) (A B : NormalForm P)
    (f : G P Γ (Δ ++ A :: B :: Λ)) :
    AllBlockedAt (disjR Γ Δ Λ A B f) .right (At.shift Δ (.here (.disj A B) Λ)) :=
  allBlockedAt_of_leaf _ _ _ (disjR_principal_leaf ..)

end G
namespace PositionalCut

/-- The fresh right-premise rank is one independently of either rebuilt premise. -/
theorem rank_fresh_disjL {Γ Δ F U V W : List (NormalForm P)} {A B : NormalForm P}
    (f : G P Γ Δ) (x : At Δ (.disj A B)) (g : G P (A :: F) V) (h : G P (B :: U) W) :
    rank f x (G.disjL g h) (.here (.disj A B) (F ++ U)) = f.rho .right x + 1 := by
  unfold rank
  rw [G.rho_disjL_principal]

theorem rank_fresh_conjR {Γ Δ F U V W : List (NormalForm P)} {A B : NormalForm P}
    (f : G P F (A :: V)) (g : G P U (B :: W)) (h : G P Γ Δ) (x : At Γ (.conj A B)) :
    rank (G.conjR f g) (.here (.conj A B) (V ++ W)) h x = 1 + h.rho .left x := by
  unfold rank
  rw [G.rho_conjR_principal]

/-- Only the unchanged side and the new leaf are needed for the next rank decrease. -/
theorem rank_fresh_disjL_lt {Γ Δ Θ Λ F U V W : List (NormalForm P)} {A B : NormalForm P}
    (f : G P Γ Δ) (x : At Δ (.disj A B)) (old : G P Θ Λ) (y : At Θ (.disj A B))
    (hold : 1 < old.rho .left y) (g : G P (A :: F) V) (h : G P (B :: U) W) :
    rank f x (G.disjL g h) (.here (.disj A B) (F ++ U)) < rank f x old y := by
  rw [rank_fresh_disjL]
  unfold rank
  omega

theorem rank_fresh_conjR_lt {Γ Δ Θ Λ F U V W : List (NormalForm P)} {A B : NormalForm P}
    (old : G P Γ Δ) (x : At Δ (.conj A B)) (h : G P Θ Λ) (y : At Θ (.conj A B))
    (hold : 1 < old.rho .right x) (f : G P F (A :: V)) (g : G P U (B :: W)) :
    rank (G.conjR f g) (.here (.conj A B) (V ++ W)) h y < rank old x h y := by
  rw [rank_fresh_conjR]
  unfold rank
  omega

end PositionalCut
end DosenPetric.Reduced.Gentzen
