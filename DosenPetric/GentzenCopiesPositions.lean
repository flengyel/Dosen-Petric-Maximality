module

public import DosenPetric.GentzenPositions

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

def copyHead (C : NormalForm P) (Γ : List (NormalForm P))
    (gs : List (List (NormalForm P))) (Θ : List (NormalForm P)) :
    Route (Γ ++ (gaps gs ++ C :: Θ)) (Γ ++ C :: (repeated C gs ++ Θ)) :=
  Route.append (Route.map (fun a => a.before _) (Route.identity Γ))
    (.cons (At.shift Γ (At.shift (gaps gs) (.here C Θ)))
      (Route.map (fun a => At.shift Γ a) (copies C gs Θ)))

theorem copySource (C : NormalForm P) (Γ : List (NormalForm P))
    (gs : List (List (NormalForm P))) (Θ : List (NormalForm P)) :
    Γ ++ (gaps gs ++ C :: Θ) = gaps (Γ :: gs) ++ C :: Θ := by
  simp only [gaps, List.append_assoc]

theorem copyTarget (C : NormalForm P) (Γ : List (NormalForm P))
    (gs : List (List (NormalForm P))) (Θ : List (NormalForm P)) :
    Γ ++ C :: (repeated C gs ++ Θ) = repeated C (Γ :: gs) ++ Θ := by
  simp only [repeated, List.append_assoc, List.cons_append]

theorem copies_cast (C : NormalForm P) (Γ : List (NormalForm P))
    (gs : List (List (NormalForm P))) (Θ : List (NormalForm P)) :
    copies C (Γ :: gs) Θ = (copyHead C Γ gs Θ).cast (copySource C Γ gs Θ) (copyTarget C Γ gs Θ) := by
  unfold copies
  apply eq_of_heq
  change (cast _ (copyHead C Γ gs Θ)) ≍ _
  exact (cast_heq _ _).trans (Route.cast_heq ..).symm

/-- Numerical position of the retained copy; fixed positions are not label tests. -/
def copyIndex : List (List (NormalForm P)) → Nat → Nat
  | [], i => i + 1
  | Γ :: gs, i => if i < Γ.length then i else
      if i = Γ.length then Γ.length + (gaps gs).length else
        Γ.length + copyIndex gs (i - Γ.length - 1)

theorem copies_index (C : NormalForm P) (gs : List (List (NormalForm P)))
    (Θ : List (NormalForm P)) {A : NormalForm P} (a : At (repeated C gs ++ Θ) A) :
    ((copies C gs Θ).get a).index = copyIndex gs a.index := by
  induction gs with
  | nil =>
    simp only [copies, Route.get_map, Route.get_identity, At.index, copyIndex]
  | cons Γ gs ih =>
    rw [copies_cast, Route.get_index_cast]
    let b := a.cast (copyTarget C Γ gs Θ).symm
    have hb : b.index = a.index := At.index_cast _ _
    change ((copyHead C Γ gs Θ).get b).index = _
    cases At.cases_append Γ (C :: (repeated C gs ++ Θ)) b with
    | inl h =>
      obtain ⟨c, hc⟩ := h
      have hi := c.index_lt
      rw [hc]
      simp only [copyHead, Route.get_append_before, Route.get_map, Route.get_identity,
        At.index_before] at *
      simp only [copyIndex]
      rw [← hb]
      simp only [hc, At.index_before]
      simp only [ite_eq_left hi]
    | inr h =>
      obtain ⟨c, hc⟩ := h
      rw [hc]
      simp only [copyHead, Route.get_append_shift]
      cases c with
      | here =>
        simp only [Route.get, At.index_shift, At.index]
        simp only [copyIndex]
        rw [← hb]
        simp only [hc, At.index_shift, At.index]
        simp only [Nat.add_zero, Nat.lt_irrefl, ite_false, ite_true]
      | there c =>
        simp only [Route.get, Route.get_map, At.index_shift, ih]
        simp only [copyIndex]
        rw [← hb]
        simp only [hc, At.index_shift, At.index]
        have hlt : ¬ Γ.length + (c.index + 1) < Γ.length := by omega
        have hne : Γ.length + (c.index + 1) ≠ Γ.length := by omega
        rw [ite_eq_right hlt, ite_eq_right hne]
        congr 2
        omega

end DosenPetric.Reduced.Gentzen
