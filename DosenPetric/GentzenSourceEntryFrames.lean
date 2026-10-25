module

public import DosenPetric.GentzenEntryFrameRules
public import DosenPetric.GentzenParentIndices

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

namespace EntryFrame
variable {C : NormalForm P}

theorem contraction_left (D : NormalForm P) (gs : List (List (NormalForm P)))
    (Θ Δ : List (NormalForm P)) (hn : 2 ≤ gs.length)
    (f : G P (repeated D gs++Θ) Δ)
    (hf : EntryFrame .left D f (fun x => x.index ∈ copyOffsets gs))
    {A : NormalForm P} (x : At (gaps gs++D::Θ) A)
    (hx : (G.contractL D gs Θ Δ hn f).LowerContraction .left x)
    {I J : List (NormalForm P)} {t : G P I J}
    (p : Premise (G.contractL D gs Θ Δ hn f) t) :
    EntryFrame .left A t (fun u => p.parent .left u = some x) := by
  let keep := At.shift (gaps gs) (.here D Θ)
  have hidx := G.lowerContraction_index_unique _ .left x keep hx (G.LowerContraction.left ..)
  cases he : At.compare x keep with
  | apart h => exact False.elim (h hidx)
  | same =>
    have hb := G.branches_complete (⟨I,J,t,p⟩ : Branch (G.contractL D gs Θ Δ hn f))
    simp only [G.branches,List.mem_singleton] at hb
    cases hb
    apply hf.mono
    intro u hu
    change some ((copies D gs Θ).get u) = some keep at hu
    have hm := (TraceRoute.fiber_correct (TraceRoute.full (copies D gs Θ)) keep u).mpr
      ((TraceRoute.get_full _ _).trans hu)
    rw [fiber_copies_selected] at hm
    exact (selectedCopies_mem D gs Θ u).mp hm

theorem contraction_right (Γ : List (NormalForm P)) (D : NormalForm P)
    (gs : List (List (NormalForm P))) (Λ : List (NormalForm P)) (hn : 2 ≤ gs.length)
    (f : G P Γ (repeated D gs++Λ))
    (hf : EntryFrame .right D f (fun x => x.index ∈ copyOffsets gs))
    {A : NormalForm P} (x : At (gaps gs++D::Λ) A)
    (hx : (G.contractR Γ D gs Λ hn f).LowerContraction .right x)
    {I J : List (NormalForm P)} {t : G P I J}
    (p : Premise (G.contractR Γ D gs Λ hn f) t) :
    EntryFrame .right A t (fun u => p.parent .right u = some x) := by
  let keep := At.shift (gaps gs) (.here D Λ)
  have hidx := G.lowerContraction_index_unique _ .right x keep hx (G.LowerContraction.right ..)
  cases he : At.compare x keep with
  | apart h => exact False.elim (h hidx)
  | same =>
    have hb := G.branches_complete (⟨I,J,t,p⟩ : Branch (G.contractR Γ D gs Λ hn f))
    simp only [G.branches,List.mem_singleton] at hb
    cases hb
    apply hf.mono
    intro u hu
    change some ((copies D gs Λ).get u) = some keep at hu
    have hm := (TraceRoute.fiber_correct (TraceRoute.full (copies D gs Λ)) keep u).mpr
      ((TraceRoute.get_full _ _).trans hu)
    rw [fiber_copies_selected] at hm
    exact (selectedCopies_mem D gs Λ u).mp hm

theorem index_reindex_iff {Γ Δ Γ' Δ' : List (NormalForm P)} {g : G P Γ Δ}
    {s : SequentSide} {F : Nat → Prop} (hΓ : Γ = Γ') (hΔ : Δ = Δ') :
    EntryFrame s C (g.reindex hΓ hΔ) (fun x => F x.index) ↔
      EntryFrame s C g (fun x => F x.index) := by
  cases hΓ; cases hΔ; rfl

theorem exchange_head_index (n i : Nat) (hi : 1 ≤ i) (hl : i < 1+n) :
    exchangeIndex 0 1 n i = i-1 := by
  unfold exchangeIndex
  repeat first | split | omega

theorem source_disj_left {Γ Θ Δ Λ : List (NormalForm P)} {A B : NormalForm P}
    (f : G P (Γ++[A]) Δ) (g : G P (Θ++[B]) Λ) (F : Nat → Prop)
    (hl : UniqueOn F 0 Γ.length) (hr : UniqueOn F Γ.length (Γ.length+Θ.length)) :
    EntryFrame .left C (BlockedSource.disjLLast f g) (fun x => F x.index) := by
  unfold BlockedSource.disjLLast
  apply index_reindex
  apply exchange_left _ .left F
  change EntryFrame .left C _ (fun x => F (exchangeIndex 0 1 (Γ++Θ).length x.index))
  apply index_reindex (F := fun i => F (exchangeIndex 0 1 (Γ++Θ).length i))
  apply disj_left (F := fun i => F (exchangeIndex 0 1 (Γ++Θ).length i))
  · intro i j hi hj hil hir hjl hjr
    change F (exchangeIndex 0 1 (Γ++Θ).length i) at hi
    change F (exchangeIndex 0 1 (Γ++Θ).length j) at hj
    simp only [List.length_append] at hi hj
    rw [exchange_head_index _ i hil (by omega)] at hi
    rw [exchange_head_index _ j hjl (by omega)] at hj
    have he := hl (i-1) (j-1) hi hj (by omega) (by omega) (by omega) (by omega)
    omega
  · intro i j hi hj hil hir hjl hjr
    change F (exchangeIndex 0 1 (Γ++Θ).length i) at hi
    change F (exchangeIndex 0 1 (Γ++Θ).length j) at hj
    simp only [List.length_append] at hi hj
    rw [exchange_head_index _ i (by omega) (by omega)] at hi
    rw [exchange_head_index _ j (by omega) (by omega)] at hj
    have he := hr (i-1) (j-1) hi hj (by omega) (by omega) (by omega) (by omega)
    omega

theorem source_disj_right {Γ Θ Δ Λ : List (NormalForm P)} {A B : NormalForm P}
    (f : G P (Γ++[A]) Δ) (g : G P (Θ++[B]) Λ) (F : Nat → Prop)
    (hl : UniqueOn F 0 Δ.length) (hr : UniqueOn F Δ.length (Δ.length+Λ.length)) :
    EntryFrame .right C (BlockedSource.disjLLast f g) (fun x => F x.index) := by
  unfold BlockedSource.disjLLast
  apply index_reindex
  apply exchange_left _ .right F
  change EntryFrame .right C _ (fun x => F x.index)
  apply index_reindex
  exact disj_right _ _ F hl hr

end EntryFrame
end DosenPetric.Reduced.Gentzen
