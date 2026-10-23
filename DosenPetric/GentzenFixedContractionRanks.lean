module

public import DosenPetric.GentzenInsertionRouting

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

namespace G

theorem rho_reindex_left {Γ Δ Γ' Δ' : List (NormalForm P)} (hΓ : Γ = Γ') (hΔ : Δ = Δ')
    (g : G P Γ Δ) {A : NormalForm P} (x : At Γ A) :
    (g.reindex hΓ hΔ).rho .left (x.cast hΓ) = g.rho .left x := by cases hΓ; cases hΔ; rfl

theorem rho_reindex_right {Γ Δ Γ' Δ' : List (NormalForm P)} (hΓ : Γ = Γ') (hΔ : Δ = Δ')
    (g : G P Γ Δ) {A : NormalForm P} (x : At Δ A) :
    (g.reindex hΓ hΔ).rho .right (x.cast hΔ) = g.rho .right x := by cases hΓ; cases hΔ; rfl

theorem rho_reindex_left_at {Γ Δ Γ' Δ' : List (NormalForm P)} (hΓ : Γ = Γ') (hΔ : Δ = Δ')
    (g : G P Γ Δ) {A : NormalForm P} (x : At Γ' A) :
    (g.reindex hΓ hΔ).rho .left x = g.rho .left (x.cast hΓ.symm) := by cases hΓ; cases hΔ; rfl

theorem rho_reindex_right_at {Γ Δ Γ' Δ' : List (NormalForm P)} (hΓ : Γ = Γ') (hΔ : Δ = Δ')
    (g : G P Γ Δ) {A : NormalForm P} (x : At Δ' A) :
    (g.reindex hΓ hΔ).rho .right x = g.rho .right (x.cast hΔ.symm) := by cases hΓ; cases hΔ; rfl

theorem rho_reindex_left_back {Γ Γ' Δ : List (NormalForm P)} (h : Γ = Γ')
    (g : G P Γ' Δ) {A : NormalForm P} (x : At Γ A) :
    (g.reindex h.symm rfl).rho .left x = g.rho .left (x.cast h) := by cases h; rfl

theorem rho_reindex_right_back {Γ Δ Δ' : List (NormalForm P)} (h : Δ = Δ')
    (g : G P Γ Δ') {A : NormalForm P} (x : At Δ A) :
    (g.reindex rfl h.symm).rho .right x = g.rho .right (x.cast h) := by cases h; rfl

theorem contractionRankL_cast_eq {U Δ : List (NormalForm P)} (C : NormalForm P)
    (gs : List (List (NormalForm P))) (Θ : List (NormalForm P)) (hn : 2 ≤ gs.length)
    (h : repeated C gs ++ Θ = U) (f : G P U Δ) :
    contractionRankL C gs Θ Δ hn (f.reindex h.symm rfl) =
      1 + (((selectedCopies C gs Θ).map (At.cast h)).map
        (fun (a : At U C) => f.rho .left a)).sum := by
  have he : (selectedCopies C gs Θ).map
      (fun (a : At (repeated C gs ++ Θ) C) => (f.reindex h.symm rfl).rho .left a) =
      ((selectedCopies C gs Θ).map (At.cast h)).map (fun (a : At U C) => f.rho .left a) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro a _
    exact rho_reindex_left_back h f a
  exact (contractionRankL_eq ..).trans (congrArg (fun xs : List Nat => 1+xs.sum) he)

theorem contractionRankR_cast_eq {Γ U : List (NormalForm P)} (C : NormalForm P)
    (gs : List (List (NormalForm P))) (Θ : List (NormalForm P)) (hn : 2 ≤ gs.length)
    (h : repeated C gs ++ Θ = U) (f : G P Γ U) :
    contractionRankR Γ C gs Θ hn (f.reindex rfl h.symm) =
      1 + (((selectedCopies C gs Θ).map (At.cast h)).map
        (fun (a : At U C) => f.rho .right a)).sum := by
  have he : (selectedCopies C gs Θ).map
      (fun (a : At (repeated C gs ++ Θ) C) => (f.reindex rfl h.symm).rho .right a) =
      ((selectedCopies C gs Θ).map (At.cast h)).map (fun (a : At U C) => f.rho .right a) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro a _
    exact rho_reindex_right_back h f a
  exact (contractionRankR_eq ..).trans (congrArg (fun xs : List Nat => 1+xs.sum) he)

/-- Fixed-position contraction fiber, with its unique upper position supplied explicitly. -/
theorem contraction_fixed_left (C : NormalForm P) (gs : List (List (NormalForm P)))
    (Θ Δ : List (NormalForm P)) (hn : 2 ≤ gs.length) (f : G P (repeated C gs ++ Θ) Δ)
    {A : NormalForm P} (a : At (gaps gs ++ C :: Θ) A) (b : At (repeated C gs ++ Θ) A)
    (ha : a.index ≠ (gaps gs).length) (hb : (copies C gs Θ).get b = a) :
    (contractL C gs Θ Δ hn f).rho .left a = 1 + f.rho .left b := by
  have hm : b ∈ (TraceRoute.full (copies C gs Θ)).fiber a :=
    (TraceRoute.fiber_correct ..).mpr ((TraceRoute.get_full ..).trans (congrArg some hb))
  rw [fiber_copies_fixed C gs Θ a ha] at hm
  have he : b = fixedCopyAt C gs Θ a ha := List.mem_singleton.mp hm
  have hp : (contractL C gs Θ Δ hn f).predecessors .left a =
      [⟨⟨_,_,f,Premise.contractL C gs Θ Δ hn f⟩,b⟩] := by
    simp only [predecessors,branches,List.flatMap_cons,List.flatMap_nil,List.append_nil]
    change ((TraceRoute.full (copies C gs Θ)).fiber a).map _ = _
    rw [fiber_copies_fixed C gs Θ a ha,← he]
    rfl
  have hr := congrArg (fun us : List (Upper (contractL C gs Θ Δ hn f) .left A) =>
    1 + (us.map (fun v => v.branch.proof.rho .left v.position)).sum) hp
  exact ((contractL C gs Θ Δ hn f).rho_eq .left a).trans
    (by simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] using hr)

theorem contraction_fixed_right (Γ : List (NormalForm P)) (C : NormalForm P)
    (gs : List (List (NormalForm P))) (Λ : List (NormalForm P)) (hn : 2 ≤ gs.length)
    (f : G P Γ (repeated C gs ++ Λ)) {A : NormalForm P}
    (a : At (gaps gs ++ C :: Λ) A) (b : At (repeated C gs ++ Λ) A)
    (ha : a.index ≠ (gaps gs).length) (hb : (copies C gs Λ).get b = a) :
    (contractR Γ C gs Λ hn f).rho .right a = 1 + f.rho .right b := by
  have hm : b ∈ (TraceRoute.full (copies C gs Λ)).fiber a :=
    (TraceRoute.fiber_correct ..).mpr ((TraceRoute.get_full ..).trans (congrArg some hb))
  rw [fiber_copies_fixed C gs Λ a ha] at hm
  have he : b = fixedCopyAt C gs Λ a ha := List.mem_singleton.mp hm
  have hp : (contractR Γ C gs Λ hn f).predecessors .right a =
      [⟨⟨_,_,f,Premise.contractR Γ C gs Λ hn f⟩,b⟩] := by
    simp only [predecessors,branches,List.flatMap_cons,List.flatMap_nil,List.append_nil]
    change ((TraceRoute.full (copies C gs Λ)).fiber a).map _ = _
    rw [fiber_copies_fixed C gs Λ a ha,← he]
    rfl
  have hr := congrArg (fun us : List (Upper (contractR Γ C gs Λ hn f) .right A) =>
    1 + (us.map (fun v => v.branch.proof.rho .right v.position)).sum) hp
  exact ((contractR Γ C gs Λ hn f).rho_eq .right a).trans
    (by simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] using hr)

end G
end DosenPetric.Reduced.Gentzen
