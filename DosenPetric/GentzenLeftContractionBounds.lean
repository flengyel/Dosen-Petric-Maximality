module

public import DosenPetric.GentzenContractionBounds
public import DosenPetric.GentzenRotationInverses

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace ContractionBound
variable {C : NormalForm P} {k : Nat}

theorem exchangeL (Γ X Y Θ Δ : List (NormalForm P)) (f : G P (Γ++X++Y++Θ) Δ)
    (E : At (Γ++Y++X++Θ) C→Prop)
    (h : ContractionBound .left C k f (fun y => E (y.swapBlocks Γ X Y Θ))) :
    ContractionBound .left C k (G.exchangeL Γ X Y Θ Δ f) E := by
  apply unary (Premise.exchangeL Γ X Y Θ Δ f)
  · intro j
    simpa only [G.branches,List.mem_singleton] using G.branches_complete j
  · intro x _ hx
    have ha:=(G.lowerContraction_iff_arity _ .left x).mp hx
    simp only [G.sourceArity] at ha
    omega
  · apply h.mono
    rintro y ⟨x,hx,hp⟩
    exact (Option.some.inj hp).symm ▸ hx

theorem contractL (D : NormalForm P) (gs : List (List (NormalForm P)))
    (Θ Δ : List (NormalForm P)) (hn : 2≤gs.length) (f : G P (repeated D gs++Θ) Δ)
    (E : At (gaps gs++D::Θ) C→Prop) (hb : BlockedL (G.contractL D gs Θ Δ hn f))
    (h : ContractionBound .left C k f (fun y => E ((copies D gs Θ).get y))) :
    ContractionBound .left C k (G.contractL D gs Θ Δ hn f) E := by
  apply unary (Premise.contractL D gs Θ Δ hn f)
  · intro j
    simpa only [G.branches,List.mem_singleton] using G.branches_complete j
  · exact fun _ _ _ => hb
  · apply h.mono
    rintro y ⟨x,hx,hp⟩
    exact (Option.some.inj hp).symm ▸ hx

/-- Native disjunction-left routes only the surviving whole-formula slots. -/
theorem disjL {F U Δ Λ : List (NormalForm P)} {A B : NormalForm P}
    (f : G P (A::F) Δ) (g : G P (B::U) Λ) (E : Nat→Prop)
    (hf : ContractionBound .left C k f (fun x => 0<x.index ∧ E x.index))
    (hg : ContractionBound .left C k g (fun x => 0<x.index ∧ E (F.length+x.index))) :
    ContractionBound .left C k (G.disjL f g) (fun x => E x.index) := by
  apply step
  · intro x _ hx
    have ha:=(G.lowerContraction_iff_arity _ .left x).mp hx
    cases x <;> simp only [G.sourceArity,At.index,Nat.add_one_ne_zero,ite_true,ite_false] at ha <;> omega
  · intro j
    have hj:=G.branches_complete j
    simp only [G.branches,List.mem_cons,List.not_mem_nil,or_false] at hj
    cases hj with
    | inl h =>
      cases h
      apply hf.mono
      rintro y ⟨x,hx,hp⟩
      cases y with
      | here => cases hp
      | there y =>
        change some (y.before U).there=some x at hp
        cases Option.some.inj hp
        simp only [At.index,At.index_before] at hx ⊢
        exact ⟨by omega,hx⟩
    | inr h =>
      cases h
      apply hg.mono
      rintro y ⟨x,hx,hp⟩
      cases y with
      | here => cases hp
      | there y =>
        change some (At.shift F y).there=some x at hp
        cases Option.some.inj hp
        simp only [At.index,At.index_shift] at hx ⊢
        exact ⟨by omega,by simpa only [Nat.add_assoc] using hx⟩
end ContractionBound

namespace UnaryCast
theorem exchangeL_bound {C : NormalForm P} {k : Nat} {F U : List (NormalForm P)}
    (Γ X Y Θ : List (NormalForm P)) (hF : Γ++X++Y++Θ=F) (hU : Γ++Y++X++Θ=U)
    (Δ : List (NormalForm P)) (f : G P F Δ) (E : Nat→Prop)
    (h : ContractionBound .left C k f
      (fun y => E (exchangeIndex Γ.length X.length Y.length y.index))) :
    ContractionBound .left C k (exchangeL Γ X Y Θ hF hU Δ f) (fun x => E x.index) := by
  unfold exchangeL
  apply ContractionBound.index_reindex
  apply ContractionBound.exchangeL
  apply (ContractionBound.index_reindex (F:=fun i => E (exchangeIndex Γ.length X.length Y.length i))
    h hF.symm rfl).mono
  intro y hy
  change At (Γ++X++Y++Θ) C at y
  change E ((y.swapBlocks Γ X Y Θ).index) at hy
  rw [swapBlocks_index] at hy
  exact hy
end UnaryCast
namespace ContractionBlock
 theorem left_bound {U K : List (NormalForm P)} (d : ContractionBlock P U K)
    {C : NormalForm P} {k : Nat} (hn : 2≤d.gs.length) (Δ : List (NormalForm P))
    (f : G P U Δ) (E : Nat→Prop) (hb : BlockedL (d.applyL hn Δ f))
    (h : ContractionBound .left C k f (fun y => E (copyIndex d.gs y.index))) :
    ContractionBound .left C k (d.applyL hn Δ f) (fun x => E x.index) := by
  unfold applyL
  apply ContractionBound.index_reindex
  apply ContractionBound.contractL
  · have he : ∀ {Γ Δ Γ' Δ' : List (NormalForm P)} (g : G P Γ Δ)
        (hΓ : Γ=Γ') (hΔ : Δ=Δ'), BlockedL (g.reindex hΓ hΔ)→BlockedL g := by
      intro Γ Δ Γ' Δ' g hΓ hΔ hh
      cases hΓ; cases hΔ; exact hh
    exact he _ d.lower rfl hb
  · apply (ContractionBound.index_reindex (F:=fun i => E (copyIndex d.gs i)) h d.upper.symm rfl).mono
    intro y hy
    change At (repeated d.C d.gs++d.tail) C at y
    change E (((copies d.C d.gs d.tail).get y).index) at hy
    rw [copies_index] at hy
    exact hy
end ContractionBlock
end DosenPetric.Reduced.Gentzen

namespace DosenPetric.Reduced.Gentzen.BlockedSource
universe u
variable {P : Type u} {C : NormalForm P} {k : Nat}

theorem head_tail_bound {F Δ : List (NormalForm P)} (A : NormalForm P)
    (f : G P (A::F) Δ) (E : Nat→Prop)
    (h : ContractionBound .left C k f (fun x => E x.index)) :
    ContractionBound .left C k (headL A (tailL A f)) (fun x => E x.index) := by
  unfold headL tailL
  apply UnaryCast.exchangeL_bound [] F [A] []
  apply UnaryCast.exchangeL_bound [] [A] F [] _ _ Δ f
    (fun i => E (exchangeIndex 0 F.length 1 i))
  apply h.mono
  intro x hx
  change E (exchangeIndex 0 F.length 1 (exchangeIndex 0 1 F.length x.index)) at hx
  rwa [exchangeIndex_inverse] at hx

theorem native_source_bound {F U Δ Λ : List (NormalForm P)} {A B : NormalForm P}
    (f : G P (A::F) Δ) (g : G P (B::U) Λ) (E : Nat→Prop)
    (hf : ContractionBound .left C k f
      (fun x => 0<x.index ∧ E (exchangeIndex 0 1 (F++U).length x.index)))
    (hg : ContractionBound .left C k g
      (fun x => 0<x.index ∧ E (exchangeIndex 0 1 (F++U).length (F.length+x.index)))) :
    ContractionBound .left C k (disjLLast (tailL A f) (tailL B g)) (fun x => E x.index) := by
  rw [disjLLast_eq]
  unfold tailL
  apply UnaryCast.exchangeL_bound [] [.disj A B] (F++U) []
  apply ContractionBound.disjL _ _ (fun i => E (exchangeIndex 0 1 (F++U).length i))
  · exact head_tail_bound A f (fun i => 0<i ∧ E (exchangeIndex 0 1 (F++U).length i)) hf
  · exact head_tail_bound B g (fun i => 0<i ∧ E (exchangeIndex 0 1 (F++U).length (F.length+i))) hg

end DosenPetric.Reduced.Gentzen.BlockedSource
