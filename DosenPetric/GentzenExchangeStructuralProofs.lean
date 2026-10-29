module

public import DosenPetric.GentzenSequentialTerminalTransports

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.ExchangeScript
universe u
variable {P : Type u}

theorem structural_left {F U D : List (NormalForm P)} (p : ExchangeScript P F U) (f : G P U D) :
    p.structural.left f = p.left f := by
  induction p generalizing D with
  | identity => rfl
  | seq p q ih ihq =>
    change p.structural.left (q.structural.left f) = p.left (q.left f)
    rw [ihq,ih]
  | exchange => rfl
  | reindex hF hU p ih => cases hF; cases hU; exact ih f

theorem structural_right {F U D : List (NormalForm P)} (p : ExchangeScript P F U) (f : G P D U) :
    p.structural.right f = p.right f := by
  induction p generalizing D with
  | identity => rfl
  | seq p q ih ihq =>
    change p.structural.right (q.structural.right f) = p.right (q.right f)
    rw [ihq,ih]
  | exchange => rfl
  | reindex hF hU p ih => cases hF; cases hU; exact ih f

end DosenPetric.Reduced.Gentzen.ExchangeScript
