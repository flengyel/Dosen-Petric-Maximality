module

public import DosenPetric.GentzenSelectedBlockedBranches
public import DosenPetric.GentzenExchangeScriptRanks

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace ExchangeScript

theorem blocked_left {F U Δ : List (NormalForm P)} (p : ExchangeScript P F U)
    (f : G P U Δ) {C : NormalForm P} (a : At U C) (h : AllBlockedAt f .left a) :
    AllBlockedAt (p.left f) .left (p.get a) := by
  induction p with
  | identity => exact h
  | seq p q ih ih' => exact ih (q.left f) (q.get a) (ih' f a h)
  | exchange Γ X Y Θ =>
    apply (allBlockedAt_iff_branches _ _ _).mpr
    refine ⟨?_, ?_⟩
    · intro hl
      have hh := (G.lowerContraction_iff_arity
        (G.exchangeL Γ X Y Θ Δ f) .left (a.swapBlocks Γ X Y Θ)).mp hl
      change 2 ≤ 1 at hh
      omega
    · intro b hb
      cases b with
      | mk b z =>
        have hh : b = ⟨_,_,f,Premise.exchangeL Γ X Y Θ Δ f⟩ :=
          List.mem_singleton.mp (G.branches_complete b)
        cases hh
        change some (z.swapBlocks Γ X Y Θ) = some (a.swapBlocks Γ X Y Θ) at hb
        have hz := At.swapBlocks_injective Γ X Y Θ z a (Option.some.inj hb)
        cases hz
        change AllBlockedAt f .left a
        exact h
  | reindex hF hU p ih => cases hF; cases hU; exact ih f a h

theorem blocked_right {F U Γ : List (NormalForm P)} (p : ExchangeScript P F U)
    (f : G P Γ U) {C : NormalForm P} (a : At U C) (h : AllBlockedAt f .right a) :
    AllBlockedAt (p.right f) .right (p.get a) := by
  induction p with
  | identity => exact h
  | seq p q ih ih' => exact ih (q.right f) (q.get a) (ih' f a h)
  | exchange Δ X Y Λ =>
    apply (allBlockedAt_iff_branches _ _ _).mpr
    refine ⟨?_, ?_⟩
    · intro hl
      have hh := (G.lowerContraction_iff_arity
        (G.exchangeR Γ Δ X Y Λ f) .right (a.swapBlocks Δ X Y Λ)).mp hl
      change 2 ≤ 1 at hh
      omega
    · intro b hb
      cases b with
      | mk b z =>
        have hh : b = ⟨_,_,f,Premise.exchangeR Γ Δ X Y Λ f⟩ :=
          List.mem_singleton.mp (G.branches_complete b)
        cases hh
        change some (z.swapBlocks Δ X Y Λ) = some (a.swapBlocks Δ X Y Λ) at hb
        have hz := At.swapBlocks_injective Δ X Y Λ z a (Option.some.inj hb)
        cases hz
        change AllBlockedAt f .right a
        exact h
  | reindex hF hU p ih => cases hF; cases hU; exact ih f a h

end ExchangeScript
end DosenPetric.Reduced.Gentzen
