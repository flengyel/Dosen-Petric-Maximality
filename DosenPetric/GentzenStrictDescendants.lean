module

public import DosenPetric.GentzenReducibilityMixed

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.ReducibilityBoundary
universe u
variable {P : Type u} {C : NormalForm P} {Γ Δ Θ Λ U V : List (NormalForm P)}
variable {f : G P Γ (C::Δ)} {g : G P (C::Θ) Λ} {w h : G P U V}

theorem strict_left (a : ProofAddress g w) (x : At U C) (hr : ReducibleL f g a x)
    (hk : h.rho .left x < w.rho .left x)
    {I J : List (NormalForm P)} {v : G P I J} (b : ProofAddress h v) (y : At I C)
    (hv : ReducibleL f (a.replace h) ((a.inserted h).append b) y) :
    v.rho .left y < w.rho .left x := by
  obtain ⟨z,hz,ha⟩ := (a.replacement_cluster_iff h b .left (.here C Θ) y).mp hv.2.1.1
  have he : z=x := hr.entry_unique z ha
  cases he
  exact Nat.lt_of_le_of_lt (b.ascend_rank_le .left x y hz) hk

theorem strict_right (a : ProofAddress f w) (x : At V C) (hr : ReducibleR f g a x)
    (hk : h.rho .right x < w.rho .right x)
    {I J : List (NormalForm P)} {v : G P I J} (b : ProofAddress h v) (y : At J C)
    (hv : ReducibleR (a.replace h) g ((a.inserted h).append b) y) :
    v.rho .right y < w.rho .right x := by
  obtain ⟨z,hz,ha⟩ := (a.replacement_cluster_iff h b .right (.here C Δ) y).mp hv.2.1.1
  have he : z=x := hr.entry_unique z ha
  cases he
  exact Nat.lt_of_le_of_lt (b.ascend_rank_le .right x y hz) hk

end DosenPetric.Reduced.Gentzen.ReducibilityBoundary
