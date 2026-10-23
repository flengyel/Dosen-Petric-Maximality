module

public import DosenPetric.GentzenRewiring

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.Rewire
universe u
variable {P : Type u}

/-- Contract both entire selected copies, one formula position at a time. -/
def duplicate (Ξ Γ Θ : List (NormalForm P)) : Rewire P (Ξ ++ Γ ++ Θ) (Ξ ++ Γ ++ Γ ++ Θ) :=
  match Γ with
  | [] => (Rewire.identity (Ξ ++ Θ)).reindex (by simp only [List.append_nil])
      (by simp only [List.append_nil])
  | C :: Γ => by
    let p : Rewire P (Ξ ++ (C :: Γ) ++ Θ) ((Ξ ++ [C]) ++ Γ ++ Γ ++ Θ) :=
      (duplicate (Ξ ++ [C]) Γ Θ).reindex (by simp only [List.append_assoc, List.singleton_append]) rfl
    let q : Rewire P ((Ξ ++ [C]) ++ Γ ++ Γ ++ Θ) ((Ξ ++ Γ) ++ [C] ++ (Γ ++ Θ)) :=
      (Rewire.exchange Ξ Γ [C] (Γ ++ Θ)).reindex (by simp only [List.append_assoc]) rfl
    let r : Rewire P ((Ξ ++ Γ) ++ [C] ++ (Γ ++ Θ)) (Ξ ++ (C :: Γ) ++ (C :: Γ) ++ Θ) :=
      (Rewire.contract C [Ξ, Γ] (Γ ++ Θ) (Nat.le_refl 2)).reindex
        (by simp only [gaps, List.append_nil, List.append_assoc, List.singleton_append])
        (by simp only [repeated, List.append_assoc, List.cons_append, List.nil_append])
    exact p.seq (q.seq r)

/-- The second block is identified positionally with the first; the tail shifts back. -/
def duplicateIndex (s g i : Nat) : Nat := if i < s + g then i else i - g

theorem duplicate_index (Ξ Γ Θ : List (NormalForm P)) {A : NormalForm P}
    (a : At (Ξ ++ Γ ++ Γ ++ Θ) A) :
    ((duplicate Ξ Γ Θ).get a).index = duplicateIndex Ξ.length Γ.length a.index := by
  induction Γ generalizing Ξ with
  | nil =>
    simp only [duplicate, get, At.index_cast, duplicateIndex, List.length_nil, Nat.add_zero, Nat.sub_zero]
    split <;> rfl
  | cons C Γ ih =>
    dsimp only [duplicate]
    simp only [get, At.index_cast, copies_index, swapBlocks_index, ih, List.length_append,
      List.length_cons, List.length_nil, Nat.add_zero, copyIndex, gaps, List.append_nil,
      duplicateIndex, exchangeIndex]
    repeat first | split | omega

end DosenPetric.Reduced.Gentzen.Rewire
