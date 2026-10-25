module

public import DosenPetric.GentzenReducibilityLogical

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

def BlockedOn (s : SequentSide) {Γ Δ : List (NormalForm P)} (g : G P Γ Δ) : Prop :=
  match s with | .left => BlockedL g | .right => BlockedR g

/-- A finite structural argument bounding unblocked contractions on selected
    ancestry. A step may reject a blocked contraction without bounding its rank. -/
inductive ContractionBound (s : SequentSide) (C : NormalForm P) (k : Nat) :
    {Γ Δ : List (NormalForm P)} → (g : G P Γ Δ) → (Place s Γ Δ C → Prop) → Prop where
  | bounded {Γ Δ} {g : G P Γ Δ} {E : Place s Γ Δ C → Prop}
      (h : ∀ x, E x → g.rho s x < k) : ContractionBound s C k g E
  | step {Γ Δ} {g : G P Γ Δ} {E : Place s Γ Δ C → Prop}
      (reject : ∀ x, E x → g.LowerContraction s x → BlockedOn s g)
      (children : ∀ j : Branch g, ContractionBound s C k j.proof
        (fun y => ∃ x, E x ∧ j.occurrence.parent s y = some x)) :
      ContractionBound s C k g E

namespace ContractionBound
variable {s : SequentSide} {C : NormalForm P} {k : Nat}

theorem mono {Γ Δ : List (NormalForm P)} {g : G P Γ Δ} {E F : Place s Γ Δ C → Prop}
    (h : ContractionBound s C k g E) (hf : ∀ x, F x → E x) :
    ContractionBound s C k g F := by
  induction h with
  | bounded he => exact .bounded (fun x hx => he x (hf x hx))
  | step reject children ih =>
    apply step (fun x hx hl => reject x (hf x hx) hl)
    intro j
    apply ih j
    rintro y ⟨x,hx,hp⟩
    exact ⟨x,hf x hx,hp⟩

theorem bound {Γ Δ : List (NormalForm P)} {g : G P Γ Δ} {E : Place s Γ Δ C → Prop}
    (h : ContractionBound s C k g E) {U V : List (NormalForm P)} {w : G P U V}
    (a : ProofAddress g w) (x : Place s Γ Δ C) (hx : E x) (y : Place s U V C)
    (ha : a.ascend s y = some x) (hl : w.LowerContraction s y) (hu : ¬ BlockedOn s w) :
    w.rho s y < k := by
  induction h with
  | bounded he => exact Nat.lt_of_le_of_lt (a.ascend_rank_le s x y ha) (he x hx)
  | @step Γ Δ g E reject children ih =>
    rw [← a.spine_toAddress] at ha
    cases he : a.spine with
    | root =>
      rw [he] at ha
      change some y = some x at ha
      exact False.elim (hu (reject y ((Option.some.inj ha).symm ▸ hx) hl))
    | @down _ _ I J _ _ _ j _ p b =>
      rw [he,ProofSpine.toAddress,ProofAddress.ascend_append] at ha
      change (b.toAddress.ascend s y).bind ((ProofAddress.root.down p).ascend s) = some x at ha
      cases hb : b.toAddress.ascend s y with
      | none => simp only [hb,Option.bind_none] at ha; cases ha
      | some u =>
        have hp : p.parent s u = some x := by
          simpa only [hb,Option.bind_some,ProofAddress.ascend,Option.bind_fun_some] using ha
        exact ih (⟨I,J,j,p⟩ : Branch g) b.toAddress u ⟨x,hx,hp⟩ hb

theorem index_reindex {Γ Δ Γ' Δ' : List (NormalForm P)} {g : G P Γ Δ}
    {F : Nat → Prop} (h : ContractionBound s C k g (fun x => F x.index))
    (hΓ : Γ = Γ') (hΔ : Δ = Δ') :
    ContractionBound s C k (g.reindex hΓ hΔ) (fun x => F x.index) := by
  cases hΓ; cases hΔ; exact h

theorem index_reindex_iff {Γ Δ Γ' Δ' : List (NormalForm P)} {g : G P Γ Δ}
    {F : Nat → Prop} (hΓ : Γ = Γ') (hΔ : Δ = Δ') :
    ContractionBound s C k (g.reindex hΓ hΔ) (fun x => F x.index) ↔
      ContractionBound s C k g (fun x => F x.index) := by
  cases hΓ; cases hΔ; rfl

theorem unary {Γ Δ U V : List (NormalForm P)} {g : G P Γ Δ} {f : G P U V}
    (p : Premise g f) (hp : ∀ j : Branch g, j = ⟨U,V,f,p⟩)
    {E : Place s Γ Δ C → Prop}
    (reject : ∀ x, E x → g.LowerContraction s x → BlockedOn s g)
    (h : ContractionBound s C k f (fun y => ∃ x, E x ∧ p.parent s y = some x)) :
    ContractionBound s C k g E := by
  apply step reject
  intro j
  cases hp j
  exact h

theorem exchangeR (Δ X Y Λ Γ : List (NormalForm P)) (f : G P Γ (Δ++X++Y++Λ))
    (E : At (Δ++Y++X++Λ) C → Prop)
    (h : ContractionBound .right C k f (fun y => E (y.swapBlocks Δ X Y Λ))) :
    ContractionBound .right C k (G.exchangeR Γ Δ X Y Λ f) E := by
  apply unary (Premise.exchangeR Γ Δ X Y Λ f)
  · intro j
    simpa only [G.branches,List.mem_singleton] using G.branches_complete j
  · intro x _ hx
    have ha := (G.lowerContraction_iff_arity _ .right x).mp hx
    simp only [G.sourceArity] at ha
    omega
  · apply h.mono
    rintro y ⟨x,hx,hp⟩
    exact (Option.some.inj hp).symm ▸ hx

theorem contractR (Γ : List (NormalForm P)) (D : NormalForm P)
    (gs : List (List (NormalForm P))) (Λ : List (NormalForm P)) (hn : 2 ≤ gs.length)
    (f : G P Γ (repeated D gs++Λ)) (E : At (gaps gs++D::Λ) C → Prop)
    (hb : BlockedR (G.contractR Γ D gs Λ hn f))
    (h : ContractionBound .right C k f (fun y => E ((copies D gs Λ).get y))) :
    ContractionBound .right C k (G.contractR Γ D gs Λ hn f) E := by
  apply unary (Premise.contractR Γ D gs Λ hn f)
  · intro j
    simpa only [G.branches,List.mem_singleton] using G.branches_complete j
  · exact fun _ _ _ => hb
  · apply h.mono
    rintro y ⟨x,hx,hp⟩
    exact (Option.some.inj hp).symm ▸ hx

theorem disjR (Γ Δ Λ : List (NormalForm P)) (A B : NormalForm P)
    (f : G P Γ (Δ++A::B::Λ)) (E : At (Δ++.disj A B::Λ) C → Prop)
    (h : ContractionBound .right C k f
      (fun y => ∃ x, E x ∧ At.fixed Δ [A,B] [.disj A B] Λ y = some x)) :
    ContractionBound .right C k (G.disjR Γ Δ Λ A B f) E := by
  apply unary (Premise.disjR Γ Δ Λ A B f)
  · intro j
    simpa only [G.branches,List.mem_singleton] using G.branches_complete j
  · intro x _ hx
    have ha := (G.lowerContraction_iff_arity _ .right x).mp hx
    simp only [G.sourceArity] at ha
    split at ha <;> omega
  · exact h

end ContractionBound

namespace UnaryCast
theorem exchangeR_bound {C : NormalForm P} {k : Nat}
    {F U : List (NormalForm P)} (Δ X Y Λ : List (NormalForm P))
    (hF : Δ++X++Y++Λ = F) (hU : Δ++Y++X++Λ = U)
    (Γ : List (NormalForm P)) (f : G P Γ F) (E : Nat → Prop)
    (h : ContractionBound .right C k f
      (fun y => E (exchangeIndex Δ.length X.length Y.length y.index))) :
    ContractionBound .right C k (exchangeR Δ X Y Λ hF hU Γ f)
      (fun x => E x.index) := by
  unfold exchangeR
  apply ContractionBound.index_reindex
  apply ContractionBound.exchangeR
  apply (ContractionBound.index_reindex (F:=fun i => E (exchangeIndex Δ.length X.length Y.length i))
    h rfl hF.symm).mono
  intro y hy
  change At (Δ++X++Y++Λ) C at y
  change E ((y.swapBlocks Δ X Y Λ).index) at hy
  rw [swapBlocks_index] at hy
  exact hy
end UnaryCast

namespace ContractionBlock
theorem right_bound {U K : List (NormalForm P)} (d : ContractionBlock P U K)
    {C : NormalForm P} {k : Nat} (hn : 2 ≤ d.gs.length) (Γ : List (NormalForm P))
    (f : G P Γ U) (E : Nat → Prop) (hb : BlockedR (d.applyR hn Γ f))
    (h : ContractionBound .right C k f (fun y => E (copyIndex d.gs y.index))) :
    ContractionBound .right C k (d.applyR hn Γ f) (fun x => E x.index) := by
  unfold applyR
  apply ContractionBound.index_reindex
  apply ContractionBound.contractR
  · have he : ∀ {Γ Δ Γ' Δ' : List (NormalForm P)} (g : G P Γ Δ)
        (hΓ : Γ = Γ') (hΔ : Δ = Δ'), BlockedR (g.reindex hΓ hΔ) → BlockedR g := by
      intro Γ Δ Γ' Δ' g hΓ hΔ hh
      cases hΓ; cases hΔ; exact hh
    exact he _ rfl d.lower hb
  · apply (ContractionBound.index_reindex (F:=fun i => E (copyIndex d.gs i))
      h rfl d.upper.symm).mono
    intro y hy
    change At (repeated d.C d.gs++d.tail) C at y
    change E (((copies d.C d.gs d.tail).get y).index) at hy
    rw [copies_index] at hy
    exact hy
end ContractionBlock
end DosenPetric.Reduced.Gentzen
