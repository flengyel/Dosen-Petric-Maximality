module

public import DosenPetric.GentzenSharedContractionCommutation

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.W3.SharedContraction
universe u
variable {P : Type u} (d : Gentzen.SharedContraction.Data P)
variable (hn : 2 ≤ d.gs.length) (hm : 2 ≤ d.hs.length) (h : d.Shared)

section L
variable (Δ : List (NormalForm P)) (f : G P d.F Δ)

theorem selected_sumsL :
    (d.outer.selected.map (fun b => (innerL d hn Δ f).rho .left b)).sum =
      ((d.flat hn hm h).selected.map (fun a => f.rho .left a)).sum+d.hs.length := by
  calc
    _ = (d.outer.selected.map (fun b =>
        1+(((TraceRoute.full d.inner.route).fiber b).map (fun a => f.rho .left a)).sum)).sum := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro b _
      exact d.inner.rankL_fiber hn Δ f b
    _ = (d.outer.selected.map (fun b =>
        (((TraceRoute.full d.inner.route).fiber b).map (fun a => f.rho .left a)).sum)).sum+
        d.outer.selected.length := G.sum_map_one_add _ _
    _ = _ :=
      (congrArg (fun n : Nat => n+d.outer.selected.length)
        (d.weights hn hm h (fun a : At d.F d.C => f.rho .left a))).trans
      (congrArg (fun n : Nat =>
        ((d.flat hn hm h).selected.map (fun a : At d.F d.C => f.rho .left a)).sum+n)
        d.outer.selected_length)

theorem outer_rankL : d.outer.rankL hm Δ (innerL d hn Δ f) =
    (d.flat hn hm h).rankL (d.flat_bound hn hm h) Δ f+d.hs.length := by
  have h₀ := d.outer.rankL_sum hm Δ (innerL d hn Δ f)
  have h₁ := (d.flat hn hm h).rankL_sum (d.flat_bound hn hm h) Δ f
  have hs := selected_sumsL d hn hm h Δ f
  omega

theorem flat_endpointL : (flatL d hn hm h Δ f).rho .left d.outer.keep =
    (d.flat hn hm h).rankL (d.flat_bound hn hm h) Δ f :=
  (congrArg (fun a : At d.K d.C => (flatL d hn hm h Δ f).rho .left a)
    (d.keep hn hm h)).symm.trans ((d.flat hn hm h).rankL_keep (d.flat_bound hn hm h) Δ f)

theorem retained_rankL : (oldL d hn hm Δ f).rho .left d.outer.keep =
    (flatL d hn hm h Δ f).rho .left d.outer.keep+d.hs.length :=
  (d.outer.rankL_keep hm Δ (innerL d hn Δ f)).trans
    ((outer_rankL d hn hm h Δ f).trans
      (congrArg (fun n : Nat => n+d.hs.length) (flat_endpointL d hn hm h Δ f).symm))

theorem retained_decreasesL : (flatL d hn hm h Δ f).rho .left d.outer.keep <
    (oldL d hn hm Δ f).rho .left d.outer.keep := by
  have he := retained_rankL d hn hm h Δ f
  omega

theorem old_otherL {A : NormalForm P} (z : At d.K A) (hz : z.index ≠ d.outer.keep.index) :
    (oldL d hn hm Δ f).rho .left z = 2+f.rho .left (d.original h z hz) := by
  have h₀ := d.outer.rankL_fixed hm Δ (innerL d hn Δ f) z (d.middle z hz) hz (d.outer.fixed_get z hz)
  have h₁ := d.inner.rankL_fixed hn Δ f (d.middle z hz) (d.original h z hz)
    (d.middle_fixed h z hz) (d.inner.fixed_get _ _)
  exact h₀.trans ((congrArg (fun n : Nat => 1+n) h₁).trans (by omega))

theorem flat_otherL {A : NormalForm P} (z : At d.K A) (hz : z.index ≠ d.outer.keep.index) :
    (flatL d hn hm h Δ f).rho .left z = 1+f.rho .left (d.original h z hz) :=
  (d.flat hn hm h).rankL_fixed (d.flat_bound hn hm h) Δ f z (d.original h z hz)
    (by rw [d.keep]; exact hz) (by rw [d.square,d.original_get])

theorem other_lossL {A : NormalForm P} (z : At d.K A) (hz : z.index ≠ d.outer.keep.index) :
    (oldL d hn hm Δ f).rho .left z = (flatL d hn hm h Δ f).rho .left z+1 := by
  have h₀ := old_otherL d hn hm h Δ f z hz
  have h₁ := flat_otherL d hn hm h Δ f z hz
  omega
end L

section R
variable (Γ : List (NormalForm P)) (f : G P Γ d.F)

theorem selected_sumsR :
    (d.outer.selected.map (fun b => (innerR d hn Γ f).rho .right b)).sum =
      ((d.flat hn hm h).selected.map (fun a => f.rho .right a)).sum+d.hs.length := by
  calc
    _ = (d.outer.selected.map (fun b =>
        1+(((TraceRoute.full d.inner.route).fiber b).map (fun a => f.rho .right a)).sum)).sum := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro b _
      exact d.inner.rankR_fiber hn Γ f b
    _ = (d.outer.selected.map (fun b =>
        (((TraceRoute.full d.inner.route).fiber b).map (fun a => f.rho .right a)).sum)).sum+
        d.outer.selected.length := G.sum_map_one_add _ _
    _ = _ :=
      (congrArg (fun n : Nat => n+d.outer.selected.length)
        (d.weights hn hm h (fun a : At d.F d.C => f.rho .right a))).trans
      (congrArg (fun n : Nat =>
        ((d.flat hn hm h).selected.map (fun a : At d.F d.C => f.rho .right a)).sum+n)
        d.outer.selected_length)

theorem outer_rankR : d.outer.rankR hm Γ (innerR d hn Γ f) =
    (d.flat hn hm h).rankR (d.flat_bound hn hm h) Γ f+d.hs.length := by
  have h₀ := d.outer.rankR_sum hm Γ (innerR d hn Γ f)
  have h₁ := (d.flat hn hm h).rankR_sum (d.flat_bound hn hm h) Γ f
  have hs := selected_sumsR d hn hm h Γ f
  omega

theorem flat_endpointR : (flatR d hn hm h Γ f).rho .right d.outer.keep =
    (d.flat hn hm h).rankR (d.flat_bound hn hm h) Γ f :=
  (congrArg (fun a : At d.K d.C => (flatR d hn hm h Γ f).rho .right a)
    (d.keep hn hm h)).symm.trans ((d.flat hn hm h).rankR_keep (d.flat_bound hn hm h) Γ f)

theorem retained_rankR : (oldR d hn hm Γ f).rho .right d.outer.keep =
    (flatR d hn hm h Γ f).rho .right d.outer.keep+d.hs.length :=
  (d.outer.rankR_keep hm Γ (innerR d hn Γ f)).trans
    ((outer_rankR d hn hm h Γ f).trans
      (congrArg (fun n : Nat => n+d.hs.length) (flat_endpointR d hn hm h Γ f).symm))

theorem retained_decreasesR : (flatR d hn hm h Γ f).rho .right d.outer.keep <
    (oldR d hn hm Γ f).rho .right d.outer.keep := by
  have he := retained_rankR d hn hm h Γ f
  omega

theorem old_otherR {A : NormalForm P} (z : At d.K A) (hz : z.index ≠ d.outer.keep.index) :
    (oldR d hn hm Γ f).rho .right z = 2+f.rho .right (d.original h z hz) := by
  have h₀ := d.outer.rankR_fixed hm Γ (innerR d hn Γ f) z (d.middle z hz) hz (d.outer.fixed_get z hz)
  have h₁ := d.inner.rankR_fixed hn Γ f (d.middle z hz) (d.original h z hz)
    (d.middle_fixed h z hz) (d.inner.fixed_get _ _)
  exact h₀.trans ((congrArg (fun n : Nat => 1+n) h₁).trans (by omega))

theorem flat_otherR {A : NormalForm P} (z : At d.K A) (hz : z.index ≠ d.outer.keep.index) :
    (flatR d hn hm h Γ f).rho .right z = 1+f.rho .right (d.original h z hz) :=
  (d.flat hn hm h).rankR_fixed (d.flat_bound hn hm h) Γ f z (d.original h z hz)
    (by rw [d.keep]; exact hz) (by rw [d.square,d.original_get])

theorem other_lossR {A : NormalForm P} (z : At d.K A) (hz : z.index ≠ d.outer.keep.index) :
    (oldR d hn hm Γ f).rho .right z = (flatR d hn hm h Γ f).rho .right z+1 := by
  have h₀ := old_otherR d hn hm h Γ f z hz
  have h₁ := flat_otherR d hn hm h Γ f z hz
  omega
end R

end DosenPetric.Reduced.Gentzen.W3.SharedContraction
