module

public import DosenPetric.GentzenGapInsertionData

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

theorem thin_get_injective (Γ Θ : List (NormalForm P)) (E : NormalForm P)
    {A : NormalForm P} (a b : At (Γ ++ Θ) A)
    (h : (Route.thin Γ Θ E).get a = (Route.thin Γ Θ E).get b) : a = b := by
  apply At.index_injective
  apply GapInsertion.liftIndex_injective Γ.length
  have hi := congrArg At.index h
  simpa only [thin_index,GapInsertion.liftIndex] using hi

theorem thin_old_position (Γ Θ : List (NormalForm P)) (E : NormalForm P)
    {A : NormalForm P} (y : At (Γ ++ E :: Θ) A) (hy : y.index ≠ Γ.length) :
    ∃ a : At (Γ ++ Θ) A, (Route.thin Γ Θ E).get a = y := by
  cases h : At.fixed Γ [E] [] Θ y with
  | none => exact False.elim (hy ((At.fixed_single_none Γ Θ [] E y).mp h))
  | some a =>
    refine ⟨a,?_⟩
    have hr := (At.fixed_reverse Γ [E] [] Θ y a).mp h
    exact Option.some.inj ((thin_parent_fixed Γ Θ E a).trans hr)

theorem thin_fiber_embedded (Γ Θ : List (NormalForm P)) (E : NormalForm P)
    {A : NormalForm P} (a : At (Γ ++ Θ) A) :
    (TraceRoute.full (Route.thin Γ Θ E)).fiber ((Route.thin Γ Θ E).get a) = [a] := by
  apply TraceRoute.fiber_single
  intro b
  rw [TraceRoute.get_full,Option.some.injEq]
  exact ⟨thin_get_injective Γ Θ E b a,fun h => by cases h; rfl⟩

namespace G

theorem predecessors_thinL_embedded (Γ Θ Δ : List (NormalForm P)) (E : NormalForm P)
    (f : G P (Γ ++ Θ) Δ) {A : NormalForm P} (a : At (Γ ++ Θ) A) :
    (thinL Γ Θ Δ E f).predecessors .left ((Route.thin Γ Θ E).get a) =
      [⟨⟨_,_,f,Premise.thinL Γ Θ Δ E f⟩,a⟩] := by
  simp only [predecessors,branches,List.flatMap_cons,List.flatMap_nil,List.append_nil]
  change ((TraceRoute.full (Route.thin Γ Θ E)).fiber ((Route.thin Γ Θ E).get a)).map _ = _
  rw [thin_fiber_embedded]
  rfl

theorem predecessors_thinR_embedded (Γ Δ Λ : List (NormalForm P)) (E : NormalForm P)
    (f : G P Γ (Δ ++ Λ)) {A : NormalForm P} (a : At (Δ ++ Λ) A) :
    (thinR Γ Δ Λ E f).predecessors .right ((Route.thin Δ Λ E).get a) =
      [⟨⟨_,_,f,Premise.thinR Γ Δ Λ E f⟩,a⟩] := by
  simp only [predecessors,branches,List.flatMap_cons,List.flatMap_nil,List.append_nil]
  change ((TraceRoute.full (Route.thin Δ Λ E)).fiber ((Route.thin Δ Λ E).get a)).map _ = _
  rw [thin_fiber_embedded]
  rfl

theorem rho_thinL_embedded (Γ Θ Δ : List (NormalForm P)) (E : NormalForm P)
    (f : G P (Γ ++ Θ) Δ) {A : NormalForm P} (a : At (Γ ++ Θ) A) :
    (thinL Γ Θ Δ E f).rho .left ((Route.thin Γ Θ E).get a) = 1 + f.rho .left a := by
  have he := congrArg (fun us : List (Upper (thinL Γ Θ Δ E f) .left A) =>
    1 + (us.map (fun v => v.branch.proof.rho .left v.position)).sum)
    (predecessors_thinL_embedded Γ Θ Δ E f a)
  exact ((thinL Γ Θ Δ E f).rho_eq .left _).trans
    (by simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] using he)

theorem rho_thinR_embedded (Γ Δ Λ : List (NormalForm P)) (E : NormalForm P)
    (f : G P Γ (Δ ++ Λ)) {A : NormalForm P} (a : At (Δ ++ Λ) A) :
    (thinR Γ Δ Λ E f).rho .right ((Route.thin Δ Λ E).get a) = 1 + f.rho .right a := by
  have he := congrArg (fun us : List (Upper (thinR Γ Δ Λ E f) .right A) =>
    1 + (us.map (fun v => v.branch.proof.rho .right v.position)).sum)
    (predecessors_thinR_embedded Γ Δ Λ E f a)
  exact ((thinR Γ Δ Λ E f).rho_eq .right _).trans
    (by simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] using he)

theorem rho_thinL_principal (Γ Θ Δ : List (NormalForm P)) (E : NormalForm P)
    (f : G P (Γ ++ Θ) Δ) :
    (thinL Γ Θ Δ E f).rho .left (At.shift Γ (.here E Θ)) = 1 := by
  apply rho_leaf
  have hi : (At.shift Γ (.here E Θ)).index = Γ.length :=
    (At.index_shift Γ (.here E Θ)).trans (Nat.add_zero _)
  change (if (At.shift Γ (.here E Θ)).index = Γ.length then 0 else 1) = 0
  rw [ite_eq_left hi]

theorem rho_thinR_principal (Γ Δ Λ : List (NormalForm P)) (E : NormalForm P)
    (f : G P Γ (Δ ++ Λ)) :
    (thinR Γ Δ Λ E f).rho .right (At.shift Δ (.here E Λ)) = 1 := by
  apply rho_leaf
  have hi : (At.shift Δ (.here E Λ)).index = Δ.length :=
    (At.index_shift Δ (.here E Λ)).trans (Nat.add_zero _)
  change (if (At.shift Δ (.here E Λ)).index = Δ.length then 0 else 1) = 0
  rw [ite_eq_left hi]

end G
end DosenPetric.Reduced.Gentzen
