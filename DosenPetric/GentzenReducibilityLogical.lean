module

public import DosenPetric.GentzenReducibilityBoundary
public import DosenPetric.GentzenSelectedLogicalRanks
public import DosenPetric.GentzenBlockedEntryFrames

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

theorem G.reindex_trans {Γ Δ Γ' Δ' Γ'' Δ'' : List (NormalForm P)}
    (g : G P Γ Δ) (hΓ : Γ = Γ') (hΔ : Δ = Δ')
    (kΓ : Γ' = Γ'') (kΔ : Δ' = Δ'') :
    (g.reindex hΓ hΔ).reindex kΓ kΔ = g.reindex (hΓ.trans kΓ) (hΔ.trans kΔ) := by
  cases hΓ; cases hΔ; cases kΓ; cases kΔ; rfl

theorem BlockedL.reindex {Γ Δ Γ' Δ' : List (NormalForm P)} {g : G P Γ Δ}
    (h : BlockedL g) (hΓ : Γ = Γ') (hΔ : Δ = Δ') : BlockedL (g.reindex hΓ hΔ) := by
  cases hΓ; cases hΔ; exact h

theorem BlockedR.reindex {Γ Δ Γ' Δ' : List (NormalForm P)} {g : G P Γ Δ}
    (h : BlockedR g) (hΓ : Γ = Γ') (hΔ : Δ = Δ') : BlockedR (g.reindex hΓ hΔ) := by
  cases hΓ; cases hΔ; exact h

namespace W4.SelectedLogical
variable (d : Gentzen.SelectedLogical.Data P .conj) (hn : 2 ≤ d.gs.length)
variable (Δ : List (NormalForm P)) (f : G P d.F Δ)

theorem new_blockedL : BlockedL (newL d hn Δ f) := by
  have h := BlockedL.conjunction d.A d.B (gaps d.gs) d.Θ Δ (innerL d hn Δ f)
  simpa only [newL,middleL,ContractionBlock.applyL,BlockedSource.left2,
    BlockedSource.conjLLast,G.reindex_trans] using h.reindex d.lastTarget rfl

/-- Terminal-left W4 at an arbitrary actual proof occurrence. -/
theorem addressed_left
    {Γ Ξ Θ Λ : List (NormalForm P)} {cutLeft : G P Γ (d.C::Ξ)}
    {root : G P (d.C::Θ) Λ}
    (a : ProofAddress root (oldL d hn Δ f))
    (hr : ReducibleL cutLeft root a d.x) :
    (newL d hn Δ f).CutFree ∧
    ofTerm (newL d hn Δ f).denote = ofTerm (oldL d hn Δ f).denote ∧
    ofTerm (a.replace (newL d hn Δ f)).denote = ofTerm root.denote ∧
    ∀ {I J : List (NormalForm P)} {v : G P I J}
      (b : ProofAddress (newL d hn Δ f) v) (y : At I d.C),
      ReducibleL cutLeft (a.replace (newL d hn Δ f))
        ((a.inserted (newL d hn Δ f)).append b) y →
      v.rho .left y < (oldL d hn Δ f).rho .left d.x := by
  have hf : f.CutFree := (old_cutFreeL d hn Δ f).mp hr.cutFree
  refine ⟨(new_cutFreeL d hn Δ f).mpr hf,denoteL d hn Δ f,
    a.replace_denote _ (denoteL d hn Δ f),?_⟩
  intro I J v b y hv
  exact ReducibilityBoundary.descendants_left a d.x _ (new_blockedL d hn Δ f)
    hr.entry_unique (endpoint_leL d hn Δ f) b y hv

/-- The full descendant quantifier for this W4 replacement, under a separately
    proved injectivity condition on the containing address. This condition is
    not inferred from source reducibility. -/
theorem addressed_left_of_injective
    {Γ Ξ Θ Λ : List (NormalForm P)} {cutLeft : G P Γ (d.C::Ξ)}
    {root : G P (d.C::Θ) Λ}
    (a : ProofAddress root (oldL d hn Δ f))
    (hr : ReducibleL cutLeft root a d.x) (hi : a.InjectiveAscend .left) :
    (newL d hn Δ f).CutFree ∧
    ofTerm (newL d hn Δ f).denote = ofTerm (oldL d hn Δ f).denote ∧
    ofTerm (a.replace (newL d hn Δ f)).denote = ofTerm root.denote ∧
    ∀ {I J : List (NormalForm P)} {v : G P I J}
      (b : ProofAddress (newL d hn Δ f) v) (y : At I d.C),
      ReducibleL cutLeft (a.replace (newL d hn Δ f))
        ((a.inserted (newL d hn Δ f)).append b) y →
      v.rho .left y < (oldL d hn Δ f).rho .left d.x := by
  have hf : f.CutFree := (old_cutFreeL d hn Δ f).mp hr.cutFree
  refine ⟨(new_cutFreeL d hn Δ f).mpr hf,denoteL d hn Δ f,
    a.replace_denote _ (denoteL d hn Δ f),?_⟩
  intro I J v b y hv
  exact ReducibilityBoundary.descendants_left a d.x _ (new_blockedL d hn Δ f)
    (fun z hz => ReducibilityBoundary.entry_unique_of_injective a d.x hr hi z hz)
    (endpoint_leL d hn Δ f) b y hv

theorem addressed_left_noncontracting
    {Γ Ξ Θ Λ : List (NormalForm P)} {cutLeft : G P Γ (d.C::Ξ)}
    {root : G P (d.C::Θ) Λ}
    (a : ProofAddress root (oldL d hn Δ f))
    (hr : ReducibleL cutLeft root a d.x) (ha : a.NoncontractingPath .left) :
    ∀ {I J : List (NormalForm P)} {v : G P I J}
      (b : ProofAddress (newL d hn Δ f) v) (y : At I d.C),
      ReducibleL cutLeft (a.replace (newL d hn Δ f))
        ((a.inserted (newL d hn Δ f)).append b) y →
      v.rho .left y < (oldL d hn Δ f).rho .left d.x :=
  (addressed_left_of_injective d hn Δ f a hr (a.noncontracting_injective .left ha)).2.2.2

/-- At the cut-premise root, no containing-address hypothesis is needed.
    The two-copy W4 endpoint ranks tie; strictness for every eligible
    descendant follows from the blocked root and a nonempty trace. -/
theorem two_copy_root_left (A B : NormalForm P)
    {Γ Ξ : List (NormalForm P)} (cutLeft : G P Γ (.conj A B::Ξ))
    (premise : G P [.conj A B,.conj A B,A,B] Δ) (hf : premise.CutFree) :
    let d : Gentzen.SelectedLogical.Data P .conj := ⟨A,B,[[],[]],[]⟩
    ∃ h : G P [.conj A B] Δ,
      h.CutFree ∧
      ofTerm h.denote = ofTerm (oldL d (Nat.le_refl 2) Δ premise).denote ∧
      ∀ {I J : List (NormalForm P)} {v : G P I J}
        (b : ProofAddress h v) (y : At I (.conj A B)),
        ReducibleL cutLeft h b y →
        v.rho .left y < (oldL d (Nat.le_refl 2) Δ premise).rho .left (.here _ []) := by
  let d : Gentzen.SelectedLogical.Data P .conj := ⟨A,B,[[],[]],[]⟩
  let h := newL d (Nat.le_refl 2) Δ premise
  refine ⟨h,(new_cutFreeL d (Nat.le_refl 2) Δ premise).mpr hf,
    denoteL d (Nat.le_refl 2) Δ premise,?_⟩
  intro I J v b y hv
  apply ReducibilityBoundary.descendants_left (f := cutLeft)
    (ProofAddress.root : ProofAddress (oldL d (Nat.le_refl 2) Δ premise)
      (oldL d (Nat.le_refl 2) Δ premise)) (.here _ []) h
    (new_blockedL d (Nat.le_refl 2) Δ premise)
    (fun z hz => Option.some.inj hz) (endpoint_leL d (Nat.le_refl 2) Δ premise) b y
  change ReducibleL cutLeft h ((ProofAddress.root : ProofAddress h h).append b) y
  rw [ProofAddress.root_append]
  exact hv

end W4.SelectedLogical
end DosenPetric.Reduced.Gentzen
