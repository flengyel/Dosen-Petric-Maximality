module

public import DosenPetric.GentzenSameSideLogicalRanks

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

namespace GapLogical.Data
variable {o : Op} (d : Data P o)

def fixed0 {E : NormalForm P} (a : At d.K0 E) (ha : a.index ≠ d.keep0.index) : At d.U0 E :=
  (fixedCopyAt d.C d.gs0 d.tail0 (a.cast d.lower0.symm)
    (by simpa only [At.index_cast,keep0_index] using ha)).cast d.upper0

theorem fixed0_get {E : NormalForm P} (a : At d.K0 E) (ha : a.index ≠ d.keep0.index) : d.c0.get (d.fixed0 a ha) = a := by
  apply At.index_injective
  simp only [c0_index,fixed0,At.index_cast,fixedCopyAt_index]
  exact copyIndex_fixed d.gs0 a.index (by simpa only [keep0_index] using ha)

theorem lowerBack_fixed {E : NormalForm P} (z : At d.K1 E)
    (hp : z.index ≠ d.loBefore.length) (hk : z.index ≠ d.keep1.index) :
    (d.lowerBack z hp).index ≠ d.keep0.index := by
  have hi := At.fixed_index d.loBefore [d.A,d.B] [d.D] d.loAfter (d.lowerBack z hp)
  change (d.kParent (d.lowerBack z hp)).map At.index = parentIndex d.loBefore.length 2 1 (d.lowerBack z hp).index at hi
  rw [d.lowerBack_spec,Option.map_some] at hi
  intro he
  rw [he,d.keep0_index,d.retainedIndex] at hi
  exact hk ((Option.some.inj hi).trans d.keep1_index.symm)

def otherUpper {E : NormalForm P} (z : At d.K1 E) (hp : z.index ≠ d.loBefore.length)
    (hk : z.index ≠ d.keep1.index) : At d.U0 E := d.fixed0 (d.lowerBack z hp) (d.lowerBack_fixed z hp hk)

theorem other_image {E : NormalForm P} (z : At d.K1 E) (hp : z.index ≠ d.loBefore.length)
    (hk : z.index ≠ d.keep1.index) : (d.uParent (d.otherUpper z hp hk)).map d.c1.get = some z := by
  exact (d.square _).trans ((congrArg d.kParent (d.fixed0_get _ _)).trans (d.lowerBack_spec z hp))

def otherMiddle {E : NormalForm P} (z : At d.K1 E) (hp : z.index ≠ d.loBefore.length)
    (hk : z.index ≠ d.keep1.index) : At d.U1 E := (d.uParent (d.otherUpper z hp hk)).get (by
      have h := d.other_image z hp hk
      cases he : d.uParent (d.otherUpper z hp hk) with
      | none => rw [he,Option.map_none] at h; cases h
      | some a => rfl)

theorem otherMiddle_spec {E : NormalForm P} (z : At d.K1 E) (hp : z.index ≠ d.loBefore.length)
    (hk : z.index ≠ d.keep1.index) : d.uParent (d.otherUpper z hp hk) = some (d.otherMiddle z hp hk) :=
  (Option.some_get _).symm

theorem otherMiddle_get {E : NormalForm P} (z : At d.K1 E) (hp : z.index ≠ d.loBefore.length)
    (hk : z.index ≠ d.keep1.index) : d.c1.get (d.otherMiddle z hp hk) = z := by
  have h := d.other_image z hp hk
  rw [d.otherMiddle_spec,Option.map_some] at h
  exact Option.some.inj h

theorem principal_fiber :
    (TraceRoute.full (copies d.C d.gs1 d.tail1)).fiber (d.zLower.cast d.lower1.symm) =
      [d.zUpper.cast d.upper1.symm] := by
  have hget : (copies d.C d.gs1 d.tail1).get (d.zUpper.cast d.upper1.symm) = d.zLower.cast d.lower1.symm := by
    apply At.index_injective
    simp only [copies_index,At.index_cast,zUpper,zLower,At.index_shift,At.index,Nat.add_zero]
    exact d.principalIndex
  have hx : (d.zLower.cast d.lower1.symm).index ≠ (gaps d.gs1).length := by
    simp only [At.index_cast,zLower,At.index_shift,At.index,Nat.add_zero]
    exact d.principalDistinct
  have hm : d.zUpper.cast d.upper1.symm ∈
      (TraceRoute.full (copies d.C d.gs1 d.tail1)).fiber (d.zLower.cast d.lower1.symm) :=
    (TraceRoute.fiber_correct ..).mpr ((TraceRoute.get_full ..).trans (congrArg some hget))
  rw [fiber_copies_fixed d.C d.gs1 d.tail1 _ hx] at hm ⊢
  rw [List.mem_singleton.mp hm]

end GapLogical.Data

namespace W1.SameSideLogical

section Left
variable (d : GapLogical.Data P .conj) (hn : 2 ≤ d.gs0.length)
variable (Δ : List (NormalForm P)) (f : G P d.U0 Δ)

theorem principal_newL_rank : (newL d hn Δ f).rho .left d.zLower = 1 :=
  G.rho_conjL_principal d.loBefore d.loAfter Δ d.A d.B (innerL d hn Δ f)

theorem principal_oldL_rank : (oldL d hn Δ f).rho .left d.zLower = 2 := by
  have h := contractL_cast_fixed_rank d.C d.gs1 d.tail1 (modifiedArity d hn) d.lower1 d.upper1
    (G.conjL d.upBefore d.upAfter Δ d.A d.B f) d.zLower d.zUpper
    (by simpa only [GapLogical.Data.zLower,At.index_shift,At.index,Nat.add_zero] using d.principalDistinct) d.principal
  exact h.trans (congrArg (fun n : Nat => 1+n) (G.rho_conjL_principal d.upBefore d.upAfter Δ d.A d.B f))

theorem other_oldL_rank {E : NormalForm P} (z : At d.K1 E)
    (hp : z.index ≠ d.loBefore.length) (hk : z.index ≠ d.keep1.index) :
    (oldL d hn Δ f).rho .left z = 2 + f.rho .left (d.otherUpper z hp hk) := by
  have h := contractL_cast_fixed_rank d.C d.gs1 d.tail1 (modifiedArity d hn) d.lower1 d.upper1
    (G.conjL d.upBefore d.upAfter Δ d.A d.B f) z (d.otherMiddle z hp hk)
    (by simpa only [GapLogical.Data.keep1_index] using hk) (d.otherMiddle_get z hp hk)
  have he : (G.conjL d.upBefore d.upAfter Δ d.A d.B f).rho .left (d.otherMiddle z hp hk) =
      1 + f.rho .left (d.otherUpper z hp hk) :=
    G.rho_conjL_surviving d.upBefore d.upAfter Δ d.A d.B f _ _ (d.otherMiddle_spec z hp hk)
  exact h.trans ((congrArg (fun n : Nat => 1+n) he).trans (by omega))

theorem other_newL_rank {E : NormalForm P} (z : At d.K1 E)
    (hp : z.index ≠ d.loBefore.length) (hk : z.index ≠ d.keep1.index) :
    (newL d hn Δ f).rho .left z = 2 + f.rho .left (d.otherUpper z hp hk) := by
  have h := G.rho_conjL_surviving d.loBefore d.loAfter Δ d.A d.B (innerL d hn Δ f) (d.lowerBack z hp) z (d.lowerBack_spec z hp)
  have he := contractL_cast_fixed_rank d.C d.gs0 d.tail0 hn d.lower0 d.upper0 f
    (d.lowerBack z hp) (d.otherUpper z hp hk)
    (by simpa only [GapLogical.Data.keep0_index] using d.lowerBack_fixed z hp hk) (d.fixed0_get _ _)
  exact h.trans ((congrArg (fun n : Nat => 1+n) he).trans (by omega))

theorem other_rankL {E : NormalForm P} (z : At d.K1 E)
    (hp : z.index ≠ d.loBefore.length) (hk : z.index ≠ d.keep1.index) :
    (newL d hn Δ f).rho .left z = (oldL d hn Δ f).rho .left z :=
  (other_newL_rank d hn Δ f z hp hk).trans (other_oldL_rank d hn Δ f z hp hk).symm

end Left

section Right
variable (d : GapLogical.Data P .disj) (hn : 2 ≤ d.gs0.length)
variable (Γ : List (NormalForm P)) (f : G P Γ d.U0)

theorem principal_newR_rank : (newR d hn Γ f).rho .right d.zLower = 1 :=
  G.rho_disjR_principal Γ d.loBefore d.loAfter d.A d.B (innerR d hn Γ f)

theorem principal_oldR_rank : (oldR d hn Γ f).rho .right d.zLower = 2 := by
  have h := contractR_cast_fixed_rank d.C d.gs1 d.tail1 (modifiedArity d hn) d.lower1 d.upper1
    (G.disjR Γ d.upBefore d.upAfter d.A d.B f) d.zLower d.zUpper
    (by simpa only [GapLogical.Data.zLower,At.index_shift,At.index,Nat.add_zero] using d.principalDistinct) d.principal
  exact h.trans (congrArg (fun n : Nat => 1+n) (G.rho_disjR_principal Γ d.upBefore d.upAfter d.A d.B f))

theorem other_oldR_rank {E : NormalForm P} (z : At d.K1 E)
    (hp : z.index ≠ d.loBefore.length) (hk : z.index ≠ d.keep1.index) :
    (oldR d hn Γ f).rho .right z = 2 + f.rho .right (d.otherUpper z hp hk) := by
  have h := contractR_cast_fixed_rank d.C d.gs1 d.tail1 (modifiedArity d hn) d.lower1 d.upper1
    (G.disjR Γ d.upBefore d.upAfter d.A d.B f) z (d.otherMiddle z hp hk)
    (by simpa only [GapLogical.Data.keep1_index] using hk) (d.otherMiddle_get z hp hk)
  have he : (G.disjR Γ d.upBefore d.upAfter d.A d.B f).rho .right (d.otherMiddle z hp hk) =
      1 + f.rho .right (d.otherUpper z hp hk) :=
    G.rho_disjR_surviving Γ d.upBefore d.upAfter d.A d.B f _ _ (d.otherMiddle_spec z hp hk)
  exact h.trans ((congrArg (fun n : Nat => 1+n) he).trans (by omega))

theorem other_newR_rank {E : NormalForm P} (z : At d.K1 E)
    (hp : z.index ≠ d.loBefore.length) (hk : z.index ≠ d.keep1.index) :
    (newR d hn Γ f).rho .right z = 2 + f.rho .right (d.otherUpper z hp hk) := by
  have h := G.rho_disjR_surviving Γ d.loBefore d.loAfter d.A d.B (innerR d hn Γ f) (d.lowerBack z hp) z (d.lowerBack_spec z hp)
  have he := contractR_cast_fixed_rank d.C d.gs0 d.tail0 hn d.lower0 d.upper0 f
    (d.lowerBack z hp) (d.otherUpper z hp hk)
    (by simpa only [GapLogical.Data.keep0_index] using d.lowerBack_fixed z hp hk) (d.fixed0_get _ _)
  exact h.trans ((congrArg (fun n : Nat => 1+n) he).trans (by omega))

theorem other_rankR {E : NormalForm P} (z : At d.K1 E)
    (hp : z.index ≠ d.loBefore.length) (hk : z.index ≠ d.keep1.index) :
    (newR d hn Γ f).rho .right z = (oldR d hn Γ f).rho .right z :=
  (other_newR_rank d hn Γ f z hp hk).trans (other_oldR_rank d hn Γ f z hp hk).symm

end Right

end W1.SameSideLogical
end DosenPetric.Reduced.Gentzen
