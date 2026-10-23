module

public import DosenPetric.GentzenPositions

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

namespace At

def splitAppend (Γ Δ : List (NormalForm P)) {A : NormalForm P} : At (Γ ++ Δ) A → At Γ A ⊕ At Δ A :=
  match Γ with
  | [] => fun a => .inr a
  | B :: Γ => fun a => match a with
    | .here _ _ => .inl (.here B Γ)
    | .there a => match splitAppend Γ Δ a with
      | .inl b => .inl b.there
      | .inr b => .inr b

theorem splitAppend_before {Γ : List (NormalForm P)} (Δ : List (NormalForm P))
    {A : NormalForm P} (a : At Γ A) : splitAppend Γ Δ (a.before Δ) = .inl a := by
  induction a with
  | here => rfl
  | there a ih => simp only [At.before, splitAppend, ih]

theorem splitAppend_shift (Γ : List (NormalForm P)) {Δ : List (NormalForm P)}
    {A : NormalForm P} (a : At Δ A) : splitAppend Γ Δ (At.shift Γ a) = .inr a := by
  induction Γ with
  | nil => rfl
  | cons B Γ ih => simp only [At.shift, splitAppend, ih]

/-- Move only the selected blocks; fixed occurrences keep their positional identities. -/
def swapBlocks (Γ X Y Θ : List (NormalForm P)) {A : NormalForm P}
    (a : At (Γ ++ X ++ Y ++ Θ) A) : At (Γ ++ Y ++ X ++ Θ) A :=
  match splitAppend (Γ ++ X ++ Y) Θ a with
  | .inr b => At.shift (Γ ++ Y ++ X) b
  | .inl b => match splitAppend (Γ ++ X) Y b with
    | .inr c => ((At.shift Γ c).before X).before Θ
    | .inl c => match splitAppend Γ X c with
      | .inr d => (At.shift (Γ ++ Y) d).before Θ
      | .inl d => ((d.before Y).before X).before Θ
end At

def exchangeIndex (g x y i : Nat) : Nat :=
  if i < g then i else if i < g + x then i + y else if i < g + x + y then i - x else i

theorem swapBlocks_index (Γ X Y Θ : List (NormalForm P)) {A : NormalForm P}
    (a : At (Γ ++ X ++ Y ++ Θ) A) :
    (a.swapBlocks Γ X Y Θ).index = exchangeIndex Γ.length X.length Y.length a.index := by
  cases At.cases_append (Γ ++ X ++ Y) Θ a with
  | inr h =>
    obtain ⟨b, rfl⟩ := h
    simp only [At.swapBlocks, At.splitAppend_shift, At.index_shift, List.length_append]
    simp only [exchangeIndex]
    split <;> (try split) <;> (try split) <;> omega
  | inl h =>
    obtain ⟨b, rfl⟩ := h
    cases At.cases_append (Γ ++ X) Y b with
    | inr h =>
      obtain ⟨c, rfl⟩ := h
      have hi := c.index_lt
      simp only [At.swapBlocks, At.splitAppend_before, At.splitAppend_shift, At.index_before,
        At.index_shift, List.length_append, exchangeIndex]
      split <;> (try split) <;> (try split) <;> omega
    | inl h =>
      obtain ⟨c, rfl⟩ := h
      cases At.cases_append Γ X c with
      | inr h =>
        obtain ⟨d, rfl⟩ := h
        have hi := d.index_lt
        simp only [At.swapBlocks, At.splitAppend_before, At.splitAppend_shift, At.index_before,
          At.index_shift, List.length_append, exchangeIndex]
        split <;> (try split) <;> (try split) <;> omega
      | inl h =>
        obtain ⟨d, rfl⟩ := h
        have hi := d.index_lt
        simp only [At.swapBlocks, At.splitAppend_before, At.index_before, exchangeIndex]
        rw [ite_eq_left hi]

def exchangeBack (o : Op) (Γ X Y Θ : List (NormalForm P)) :
    (side P o).Hom (fold o (Γ ++ Y ++ X ++ Θ)) (fold o (Γ ++ X ++ Y ++ Θ)) :=
  match o with
  | .conj => ofTerm (exchange .conj Γ X Y Θ).invTerm
  | .disj => ofTerm (exchange .disj Γ X Y Θ).toTerm

theorem exchangeBack_forward (o : Op) (Γ X Y Θ : List (NormalForm P)) :
    (side P o).comp (exchangeBack o Γ X Y Θ) (exchangeSide o Γ X Y Θ) = (side P o).id _ := by
  cases o
  · exact (exchange .conj Γ X Y Θ).inv_to
  · exact (exchange .disj Γ X Y Θ).inv_to

theorem exchangeBack_component (o : Op) (Γ X Y Θ : List (NormalForm P))
    {A : NormalForm P} (a : At (Γ ++ X ++ Y ++ Θ) A) :
    (side P o).comp (exchangeBack o Γ X Y Θ) (component o a) =
      component o (a.swapBlocks Γ X Y Θ) := by
  let C := side P o
  have step {b : At (Γ ++ Y ++ X ++ Θ) A}
      (h : C.comp (exchangeSide o Γ X Y Θ) (component o b) = component o a) :
      C.comp (exchangeBack o Γ X Y Θ) (component o a) = component o b := by
    have hh := congrArg (fun k => C.comp (exchangeBack o Γ X Y Θ) k) h
    rw [← C.assoc, exchangeBack_forward, C.id_comp] at hh
    exact hh.symm
  cases At.cases_append (Γ ++ X ++ Y) Θ a with
  | inr h =>
    obtain ⟨b, rfl⟩ := h
    simp only [At.swapBlocks, At.splitAppend_shift]
    exact step (exchangeSide_tail o Γ X Y Θ b)
  | inl h =>
    obtain ⟨b, rfl⟩ := h
    cases At.cases_append (Γ ++ X) Y b with
    | inr h =>
      obtain ⟨c, rfl⟩ := h
      simp only [At.swapBlocks, At.splitAppend_before, At.splitAppend_shift]
      exact step (exchangeSide_Y o Γ X Y Θ c)
    | inl h =>
      obtain ⟨c, rfl⟩ := h
      cases At.cases_append Γ X c with
      | inr h =>
        obtain ⟨d, rfl⟩ := h
        simp only [At.swapBlocks, At.splitAppend_before, At.splitAppend_shift]
        exact step (exchangeSide_X o Γ X Y Θ d)
      | inl h =>
        obtain ⟨d, rfl⟩ := h
        simp only [At.swapBlocks, At.splitAppend_before]
        exact step (exchangeSide_prefix o X Y Θ d)

end DosenPetric.Reduced.Gentzen
