module

public import DosenPetric.GentzenEntryFrames

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

namespace ProofAddress
variable {Γ Δ Θ Λ Ξ Ω : List (NormalForm P)}
variable {root : G P Γ Δ} {w : G P Θ Λ} {v : G P Ξ Ω}

/-- The surviving whole-formula map is injective along this actual address. -/
def InjectiveAscend (a : ProofAddress root w) (s : SequentSide) : Prop :=
  ∀ {C : NormalForm P} (y z : Place s Θ Λ C) (x : Place s Γ Δ C),
    a.ascend s y = some x → a.ascend s z = some x → y = z

theorem injective_root (s : SequentSide) :
    (.root : ProofAddress root root).InjectiveAscend s := by
  intro C y z x hy hz
  exact (Option.some.inj hy).trans (Option.some.inj hz).symm

theorem injective_down (a : ProofAddress root w) (p : Premise w v) (s : SequentSide)
    (ha : a.InjectiveAscend s)
    (hp : ∀ {C : NormalForm P} (x : Place s Θ Λ C), ¬ w.LowerContraction s x) :
    (a.down p).InjectiveAscend s := by
  intro C y z x hy hz
  change (p.parent s y).bind (a.ascend s) = some x at hy
  change (p.parent s z).bind (a.ascend s) = some x at hz
  cases h₀ : p.parent s y with
  | none => simp only [h₀,Option.bind_none] at hy; cases hy
  | some u => cases h₁ : p.parent s z with
    | none => simp only [h₁,Option.bind_none] at hz; cases hz
    | some t =>
      have hu : a.ascend s u = some x := by simpa only [h₀,Option.bind_some] using hy
      have ht : a.ascend s t = some x := by simpa only [h₁,Option.bind_some] using hz
      have he := ha u t x hu ht
      cases he
      cases p.equal_parent_or_lower s u y z h₀ h₁ with
      | inl h => exact h
      | inr h => exact False.elim (hp u h)

/-- Every frame on the selected branch has no contraction on this side.
This is a syntactic sufficient condition, not a claim about all reducible sites. -/
def NoncontractingFrame (_p : Premise w v) (s : SequentSide) : Prop :=
  ∀ {C : NormalForm P} (x : Place s Θ Λ C), ¬ w.LowerContraction s x

def NoncontractingPath : {Θ Λ : List (NormalForm P)} → {w : G P Θ Λ} →
    ProofAddress root w → SequentSide → Prop
  | _,_,_,.root,_ => True
  | _,_,_,.down a p,s => a.NoncontractingPath s ∧ NoncontractingFrame p s

theorem noncontracting_injective (a : ProofAddress root w) (s : SequentSide)
    (ha : a.NoncontractingPath s) : a.InjectiveAscend s := by
  induction a with
  | root => exact injective_root s
  | down a p ih => exact injective_down a p s (ih ha.1) ha.2

end ProofAddress

namespace ReducibilityBoundary

section Left
variable {Γ Δ Θ Λ U V : List (NormalForm P)} {C : NormalForm P}
variable {f : G P Γ (C::Δ)} {g : G P (C::Θ) Λ} {w : G P U V}
variable (a : ProofAddress g w) (x : At U C)

theorem entry_unique_of_injective (hr : ReducibleL f g a x)
    (hi : a.InjectiveAscend .left) (z : At U C)
    (hz : a.ascend .left z = some (.here C Θ)) : z = x :=
  hi z x (.here C Θ) hz (a.cluster_ascend .left (.here C Θ) x hr.2.1.1)

/-- A structural sufficient criterion for the full descendant quantifier.
It uses no rank invariance under denotation equality. -/
theorem descendants_left (h : G P U V) (hb : BlockedL h)
    (he : ∀ z : At U C, a.ascend .left z = some (.here C Θ) → z = x)
    (hrank : h.rho .left x ≤ w.rho .left x)
    {I J : List (NormalForm P)} {v : G P I J}
    (b : ProofAddress h v) (y : At I C)
    (hv : ReducibleL f (a.replace h) ((a.inserted h).append b) y) :
    v.rho .left y < w.rho .left x := by
  cases b with
  | root => exact False.elim (hv.2.2.1 hb)
  | down b p =>
    obtain ⟨z,hz,ha⟩ := (a.replacement_cluster_iff h (b.down p) .left (.here C Θ) y).mp hv.2.1.1
    have hx : z = x := he z ha
    cases hx
    have hp : (b.down p).path ≠ [] := by
      intro hh
      have hl := congrArg List.length hh
      simp only [ProofAddress.path,List.length_append,List.length_cons,List.length_nil] at hl
      omega
    exact Nat.lt_of_lt_of_le ((b.down p).ascend_rank_lt .left x y hz hp) hrank

end Left

section Right
variable {Γ Δ Θ Λ U V : List (NormalForm P)} {C : NormalForm P}
variable {f : G P Γ (C::Δ)} {g : G P (C::Θ) Λ} {w : G P U V}
variable (a : ProofAddress f w) (x : At V C)

theorem entry_unique_of_injective_right (hr : ReducibleR f g a x)
    (hi : a.InjectiveAscend .right) (z : At V C)
    (hz : a.ascend .right z = some (.here C Δ)) : z = x :=
  hi z x (.here C Δ) hz (a.cluster_ascend .right (.here C Δ) x hr.2.1.1)

theorem descendants_right (h : G P U V) (hb : BlockedR h)
    (he : ∀ z : At V C, a.ascend .right z = some (.here C Δ) → z = x)
    (hrank : h.rho .right x ≤ w.rho .right x)
    {I J : List (NormalForm P)} {v : G P I J}
    (b : ProofAddress h v) (y : At J C)
    (hv : ReducibleR (a.replace h) g ((a.inserted h).append b) y) :
    v.rho .right y < w.rho .right x := by
  cases b with
  | root => exact False.elim (hv.2.2.1 hb)
  | down b p =>
    obtain ⟨z,hz,ha⟩ := (a.replacement_cluster_iff h (b.down p) .right (.here C Δ) y).mp hv.2.1.1
    have hx : z = x := he z ha
    cases hx
    have hp : (b.down p).path ≠ [] := by
      intro hh
      have hl := congrArg List.length hh
      simp only [ProofAddress.path,List.length_append,List.length_cons,List.length_nil] at hl
      omega
    exact Nat.lt_of_lt_of_le ((b.down p).ascend_rank_lt .right x y hz hp) hrank

end Right
end ReducibilityBoundary
end DosenPetric.Reduced.Gentzen
