module

public import DosenPetric.GentzenSelectedPositions

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace ExchangeScript

/-- Every actual exchange contributes one node to a traced formula cluster. -/
def steps : {F U : List (NormalForm P)} → ExchangeScript P F U → Nat
  | _, _, .identity _ => 0
  | _, _, .seq p q => p.steps + q.steps
  | _, _, .exchange _ _ _ _ => 1
  | _, _, .reindex _ _ p => p.steps

theorem rho_left {F U Δ : List (NormalForm P)} (p : ExchangeScript P F U)
    (f : G P U Δ) {C : NormalForm P} (a : At U C) :
    (p.left f).rho .left (p.get a) = p.steps + f.rho .left a := by
  induction p with
  | identity => exact (Nat.zero_add _).symm
  | seq p q ih ih' =>
    change (p.left (q.left f)).rho .left (p.get (q.get a)) =
      (p.steps + q.steps) + f.rho .left a
    rw [ih, ih', Nat.add_assoc]
  | exchange Γ X Y Θ => exact G.rho_exchangeL_embedded Γ X Y Θ Δ f a
  | reindex hF hU p ih => cases hF; cases hU; exact ih f a

theorem rho_right {F U Γ : List (NormalForm P)} (p : ExchangeScript P F U)
    (f : G P Γ U) {C : NormalForm P} (a : At U C) :
    (p.right f).rho .right (p.get a) = p.steps + f.rho .right a := by
  induction p with
  | identity => exact (Nat.zero_add _).symm
  | seq p q ih ih' =>
    change (p.right (q.right f)).rho .right (p.get (q.get a)) =
      (p.steps + q.steps) + f.rho .right a
    rw [ih, ih', Nat.add_assoc]
  | exchange Δ X Y Λ => exact G.rho_exchangeR_embedded Γ Δ X Y Λ f a
  | reindex hF hU p ih => cases hF; cases hU; exact ih f a

end ExchangeScript
namespace At

theorem toHead_steps {Γ : List (NormalForm P)} {C : NormalForm P} (a : At Γ C) :
    a.toHead.steps = if a.index = 0 then 0 else 1 := by
  cases a with
  | here => rfl
  | there a =>
    change 1 = if a.index + 1 = 0 then 0 else 1
    rw [ite_eq_right (by omega)]

end At
end DosenPetric.Reduced.Gentzen
