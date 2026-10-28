module

public import DosenPetric.GentzenCutStructuralCommutation

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace StructuralProgram

def steps : {F U : List (NormalForm P)} → StructuralProgram P F U → Nat
  | _, _, .identity _ => 0
  | _, _, .seq p q => p.steps + q.steps
  | _, _, .exchange _ _ _ _ | _, _, .thin _ _ _ | _, _, .contract _ _ _ _ => 1
  | _, _, .reindex _ _ p => p.steps

theorem rho_left_opposite {F U Δ : List (NormalForm P)} (p : StructuralProgram P F U)
    (f : G P U Δ) {C : NormalForm P} (a : At Δ C) :
    (p.left f).rho .right a = p.steps + f.rho .right a := by
  induction p with
  | identity => exact (Nat.zero_add _).symm
  | seq p q ih ih' =>
    change (p.left (q.left f)).rho .right a = (p.steps + q.steps) + f.rho .right a
    rw [ih, ih', Nat.add_assoc]
  | exchange Γ X Y Θ => exact G.rho_exchangeL_right Γ X Y Θ Δ f a
  | thin Γ Θ A => exact G.rho_thinL_right Γ Θ Δ A f a
  | contract C gs Θ hn => exact G.rho_contractL_right C gs Θ Δ hn f a
  | reindex hF hU p ih => cases hF; cases hU; exact ih f

theorem rho_right_opposite {F U Γ : List (NormalForm P)} (p : StructuralProgram P F U)
    (f : G P Γ U) {C : NormalForm P} (a : At Γ C) :
    (p.right f).rho .left a = p.steps + f.rho .left a := by
  induction p with
  | identity => exact (Nat.zero_add _).symm
  | seq p q ih ih' =>
    change (p.right (q.right f)).rho .left a = (p.steps + q.steps) + f.rho .left a
    rw [ih, ih', Nat.add_assoc]
  | exchange Δ X Y Λ => exact G.rho_exchangeR_left Γ Δ X Y Λ f a
  | thin Δ Λ A => exact G.rho_thinR_left Γ Δ Λ A f a
  | contract C gs Λ hn => exact G.rho_contractR_left Γ C gs Λ hn f a
  | reindex hF hU p ih => cases hF; cases hU; exact ih f

end StructuralProgram
end DosenPetric.Reduced.Gentzen
