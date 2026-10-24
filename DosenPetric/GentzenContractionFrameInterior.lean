module

public import DosenPetric.GentzenContractionFrameRanks
public import DosenPetric.GentzenDisjointInstances

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

namespace Disjoint.Data
/-- The completed interior construction supplies the same reusable raw interface. -/
abbrev frame (d : Data P) : ContractionFrame P where
  C := d.C; E := d.E
  cgs0 := d.outer0; cgs1 := d.outer1; egs0 := d.eUpper; egs1 := d.eLower
  ct0 := d.Θ; ct1 := d.Θ; et0 := d.upAfter; et1 := d.loAfter
  F := d.F; FE := d.FE; FC := d.FC; K := d.K
  upperC0 := d.upperC0; lowerC0 := d.lowerC0; upperC1 := d.upperC1; lowerC1 := d.lowerC1
  upperE0 := d.upperE0; lowerE0 := d.lowerE0; upperE1 := d.upperE1; lowerE1 := d.lowerE1
  countC := d.countC; countE := rfl

theorem frame_distinct (d : Data P) : d.frame.xC.index ≠ d.frame.xE.index := by
  have h := d.retained_order
  change d.xC.index ≠ d.xE.index
  omega
end Disjoint.Data

namespace W1.ContractionFrame
variable (d : Disjoint.Data P) (hn : 2 ≤ d.outer0.length) (hm : 2 ≤ d.es.length)

theorem interior_oldL_eq (Δ : List (NormalForm P)) (f : G P d.F Δ) :
    oldL d.frame hn hm Δ f = W1.DisjointContraction.oldL d hn hm Δ f := rfl

theorem interior_newL_eq (Δ : List (NormalForm P)) (f : G P d.F Δ) :
    newL d.frame hn hm Δ f = W1.DisjointContraction.newL d hn hm Δ f := rfl

theorem interior_oldR_eq (Γ : List (NormalForm P)) (f : G P Γ d.F) :
    oldR d.frame hn hm Γ f = W1.DisjointContraction.oldR d hn hm Γ f := rfl

theorem interior_newR_eq (Γ : List (NormalForm P)) (f : G P Γ d.F) :
    newR d.frame hn hm Γ f = W1.DisjointContraction.newR d hn hm Γ f := rfl

theorem interior_rankC (Δ : List (NormalForm P)) (f : G P d.F Δ) :
    (W1.DisjointContraction.oldL d hn hm Δ f).rho .left d.xC =
      W1.DisjointContraction.LCL d hn Δ f+d.outer0.length :=
  old_xCL d.frame d.square d.e1_keepC0 d.c1_keepE0 d.frame_distinct hn hm Δ f

theorem interior_sumR (Γ : List (NormalForm P)) (f : G P Γ d.F) :
    W1.DisjointContraction.endpointSumR d Γ (W1.DisjointContraction.oldR d hn hm Γ f)+d.es.length =
    W1.DisjointContraction.endpointSumR d Γ (W1.DisjointContraction.newR d hn hm Γ f)+d.outer0.length :=
  sum_balanceR d.frame d.square d.e1_keepC0 d.c1_keepE0 d.frame_distinct hn hm Γ f

end W1.ContractionFrame
end DosenPetric.Reduced.Gentzen
