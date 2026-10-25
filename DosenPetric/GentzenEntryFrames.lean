module

public import DosenPetric.GentzenClusterTransport

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

/-- A finite rule frame separates its entry positions before any contraction
    of C on side s.
    The terminal premises may themselves contain arbitrary contractions. -/
inductive EntryFrame (s : SequentSide) (C : NormalForm P) :
    {Γ Δ : List (NormalForm P)} → (g : G P Γ Δ) → (Place s Γ Δ C → Prop) → Prop where
  | single {Γ Δ} {g : G P Γ Δ} {E : Place s Γ Δ C → Prop}
      (h : ∀ x y, E x → E y → x = y) : EntryFrame s C g E
  | step {Γ Δ} {g : G P Γ Δ} {E : Place s Γ Δ C → Prop}
      (hn : ∀ x : Place s Γ Δ C, ¬ G.LowerContraction g s x)
      (children : ∀ j : Branch g, EntryFrame s C j.proof
        (fun y => ∃ x, E x ∧ j.occurrence.parent s y = some x)) : EntryFrame s C g E

namespace EntryFrame
variable {s : SequentSide} {C : NormalForm P}

theorem mono {Γ Δ : List (NormalForm P)} {g : G P Γ Δ} {E F : Place s Γ Δ C → Prop}
    (e : EntryFrame s C g E) (h : ∀ x, F x → E x) : EntryFrame s C g F := by
  induction e with
  | single hs => exact .single (fun x y hx hy => hs x y (h x hx) (h y hy))
  | step hn children ih =>
    apply step hn
    intro j
    apply ih j
    rintro y ⟨x,hx,hp⟩
    exact ⟨x,h x hx,hp⟩

theorem index_reindex {Γ Δ Γ' Δ' : List (NormalForm P)} {g : G P Γ Δ}
    {F : Nat → Prop} (e : EntryFrame s C g (fun x => F x.index))
    (hΓ : Γ = Γ') (hΔ : Δ = Δ') :
    EntryFrame s C (g.reindex hΓ hΔ) (fun x => F x.index) := by
  cases hΓ; cases hΔ; exact e

theorem of_index {Γ Δ : List (NormalForm P)} {g : G P Γ Δ} {E : Place s Γ Δ C → Prop}
    (n : Nat) (h : ∀ x, E x → x.index = n) : EntryFrame s C g E := by
  apply single
  intro x y hx hy
  have he := (h x hx).trans (h y hy).symm
  cases s <;> exact At.index_injective x y he

theorem unique_origins {Γ Δ : List (NormalForm P)} {g : G P Γ Δ}
    {E : Place s Γ Δ C → Prop} (e : EntryFrame s C g E)
    {U V : List (NormalForm P)} {w : G P U V} (a : ProofAddress g w)
    (t : Place s U V C) (hw : G.LowerContraction w s t)
    (y z : Place s U V C) (x x' : Place s Γ Δ C) (hx : E x) (hx' : E x')
    (hy : a.ascend s y = some x) (hz : a.ascend s z = some x') : x = x' := by
  induction e with
  | single hs => exact hs x x' hx hx'
  | @step Γ Δ g E hn children ih =>
    rw [← a.spine_toAddress] at hy hz
    cases he : a.spine with
    | root => exact False.elim (hn t hw)
    | @down _ _ I J _ _ _ j _ p b =>
      rw [he,ProofSpine.toAddress,ProofAddress.ascend_append] at hy hz
      change (b.toAddress.ascend s y).bind ((ProofAddress.root.down p).ascend s) = some x at hy
      change (b.toAddress.ascend s z).bind ((ProofAddress.root.down p).ascend s) = some x' at hz
      cases h₀ : b.toAddress.ascend s y with
      | none => simp only [h₀,Option.bind_none] at hy; cases hy
      | some u =>
        cases h₁ : b.toAddress.ascend s z with
        | none => simp only [h₁,Option.bind_none] at hz; cases hz
        | some v =>
          have hp : p.parent s u = some x := by simpa [h₀,ProofAddress.ascend] using hy
          have hq : p.parent s v = some x' := by simpa [h₁,ProofAddress.ascend] using hz
          have huv : u = v := ih (⟨I,J,j,p⟩ : Branch g) b.toAddress u v
            ⟨x,hx,hp⟩ ⟨x',hx',hq⟩ h₀ h₁
          cases huv
          exact Option.some.inj (hp.symm.trans hq)

end EntryFrame

namespace Premise
theorem equal_parent_or_lower {Γ Δ Θ Λ : List (NormalForm P)} {g : G P Γ Δ} {h : G P Θ Λ}
    (p : Premise g h) (s : SequentSide) {C : NormalForm P}
    (x : Place s Γ Δ C) (y z : Place s Θ Λ C)
    (hy : p.parent s y = some x) (hz : p.parent s z = some x) :
    y = z ∨ G.LowerContraction g s x := by
  have h₀ : g.IsPredecessor s x (⟨⟨Θ,Λ,h,p⟩,y⟩ : Upper g s C) := hy
  have h₁ : g.IsPredecessor s x (⟨⟨Θ,Λ,h,p⟩,z⟩ : Upper g s C) := hz
  cases g.position_classification s x with
  | inl hf => exact False.elim ((g.leaf_iff_no_predecessor s x).mp hf _ h₀)
  | inr hp =>
    cases hp with
    | inr hc => exact .inr hc
    | inl hp =>
      obtain ⟨_,_,hu⟩ := g.parametric_unique s x hp
      have he : (⟨⟨Θ,Λ,h,p⟩,y⟩ : Upper g s C) = ⟨⟨Θ,Λ,h,p⟩,z⟩ :=
        ((hu _).mp h₀).trans ((hu _).mp h₁).symm
      apply Or.inl
      cases s <;> exact At.index_injective y z (congrArg (fun u => u.position.index) he)
end Premise

namespace EntryFrame
theorem immediate {Γ Δ : List (NormalForm P)} {g : G P Γ Δ}
    {s : SequentSide} {C : NormalForm P} {E : Place s Γ Δ C → Prop}
    (hn : ∀ x : Place s Γ Δ C, ¬ G.LowerContraction g s x)
    (hs : ∀ (j : Branch g) (x x' : Place s Γ Δ C)
      (y z : Place s j.source j.target C), E x → E x' →
      j.occurrence.parent s y = some x → j.occurrence.parent s z = some x' → x = x') :
    EntryFrame s C g E := by
  apply step hn
  intro j
  apply single
  rintro y z ⟨x,hx,hy⟩ ⟨x',hx',hz⟩
  have he := hs j x x' y z hx hx' hy hz
  cases he
  cases j.occurrence.equal_parent_or_lower s x y z hy hz with
  | inl h => exact h
  | inr h => exact False.elim (hn x h)
end EntryFrame

end DosenPetric.Reduced.Gentzen
