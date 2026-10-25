module

public import DosenPetric.GentzenSelectionDispatch

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

namespace At
theorem list_there {Γ : List (NormalForm P)} {A C : NormalForm P}
    (xs : List (At (A::Γ) C)) (h : ∀ a ∈ xs, 0 < a.index) :
    ∃ ys : List (At Γ C), xs = ys.map At.there := by
  induction xs with
  | nil => exact ⟨[],rfl⟩
  | cons a xs ih =>
    obtain ⟨ys,hy⟩ := ih (fun a ha => h a (List.mem_cons_of_mem _ ha))
    cases a with
    | here => have hh := h (.here _ _) List.mem_cons_self; cases hh
    | there a => exact ⟨a::ys,congrArg (List.cons a.there) hy⟩

theorem ordered_of_there {Γ : List (NormalForm P)} {A C : NormalForm P}
    {xs : List (At Γ C)} (h : Ordered (xs.map (@At.there P C A Γ))) : Ordered xs := by
  exact (List.pairwise_map.mp h).imp (fun {a b} hab => by
    simp only [At.index] at hab
    omega)
end At

namespace ContractionSelection
variable {C : NormalForm P}

/-- Extract the actual fixed gaps from a nonempty ordered list of selected
    whole-formula positions, without comparing formula labels. -/
theorem extract (Γ : List (NormalForm P)) (xs : List (At Γ C))
    (hn : xs ≠ []) (ho : At.Ordered xs) :
    ∃ (K : List (NormalForm P)) (p : ContractionSelection C Γ K), p.selected = xs := by
  induction Γ with
  | nil =>
    cases xs with
    | nil => exact False.elim (hn rfl)
    | cons a xs => cases a
  | cons A Γ ih =>
    cases xs with
    | nil => exact False.elim (hn rfl)
    | cons a xs =>
      cases a with
      | here =>
        cases xs with
        | nil => exact ⟨C::Γ,.last Γ,rfl⟩
        | cons b bs =>
          have ht : ∀ z ∈ b::bs, 0 < z.index := fun z hz =>
            List.rel_of_pairwise_cons ho hz
          obtain ⟨ys,hy⟩ := At.list_there (b::bs) ht
          have hyN : ys ≠ [] := by intro he; rw [he] at hy; cases hy
          have hyO : At.Ordered ys := At.ordered_of_there (by rw [←hy]; exact ho.of_cons)
          obtain ⟨K,p,hp⟩ := ih ys hyN hyO
          exact ⟨K,.more p,by simp only [selected,hp,←hy]⟩
      | there a =>
        have ht : ∀ z ∈ a.there::xs, 0 < z.index := by
          intro z hz
          cases List.mem_cons.mp hz with
          | inl he => cases he; simp only [At.index]; omega
          | inr hz =>
            have hh := List.rel_of_pairwise_cons ho hz
            simp only [At.index] at hh
            omega
        obtain ⟨ys,hy⟩ := At.list_there (a.there::xs) ht
        have hyN : ys ≠ [] := by intro he; rw [he] at hy; cases hy
        have hyO : At.Ordered ys := At.ordered_of_there (by rw [←hy]; exact ho)
        obtain ⟨K,p,hp⟩ := ih ys hyN hyO
        exact ⟨A::K,.fixed A p,by simp only [selected,hp,←hy]⟩

end ContractionSelection
end DosenPetric.Reduced.Gentzen
