module

public import DosenPetric.GentzenRightLogicalRepairBounds

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.W4.HeadRight
universe u
variable {P : Type u} (d : Gentzen.SelectedLogical.Data P .disj)
variable (hn : 2 ≤ d.gs.length) (Γ : List (NormalForm P)) (f : G P Γ d.F)

/-- Right W4 at any actual address, including two parametric copies and the
    additional fresh compound. The bound
    skips the blocked middle contraction rather than comparing root ranks. -/
theorem addressed_right
    {Ξ Δ Θ Λ : List (NormalForm P)} {root : G P Ξ (d.C::Δ)}
    {cutRight : G P (d.C::Θ) Λ}
    (a : ProofAddress root (W4.SelectedLogical.oldR d hn Γ f))
    (hr : ReducibleR root cutRight a d.x) :
    (repairR d hn Γ f).CutFree ∧
    ofTerm (repairR d hn Γ f).denote = ofTerm (W4.SelectedLogical.oldR d hn Γ f).denote ∧
    ofTerm (a.replace (repairR d hn Γ f)).denote = ofTerm root.denote ∧
    ∀ {I J : List (NormalForm P)} {v : G P I J}
      (b : ProofAddress (repairR d hn Γ f) v) (y : At J d.C),
      ReducibleR (a.replace (repairR d hn Γ f)) cutRight ((a.inserted _).append b) y →
        v.rho .right y < (W4.SelectedLogical.oldR d hn Γ f).rho .right d.x := by
  have he := denote d hn Γ f
  have hc : f.CutFree := by
    have hc := hr.cutFree
    simpa only [W4.SelectedLogical.oldR,ContractionBlock.applyR,W4.SelectedLogical.logicalR,
      G.CutFree,G.count_reindex,G.cutCount] using hc
  refine ⟨(cutFree d hn Γ f).mpr hc,he,a.replace_denote _ he,?_⟩
  intro I J v b y hv
  obtain ⟨z,hz,ha⟩ := (a.replacement_cluster_iff (repairR d hn Γ f) b .right
    (.here d.C Δ) y).mp hv.2.1.1
  have hx : z = d.x := hr.entry_unique z ha
  cases hx
  have hb := (repair_bound d hn Γ f).bound b d.x rfl y hz hv.2.1.2 hv.2.2.1
  have ho := W4.SelectedLogical.old_endpointR d hn Γ f
  omega

end DosenPetric.Reduced.Gentzen.W4.HeadRight
