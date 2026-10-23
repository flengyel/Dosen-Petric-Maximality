module

public import DosenPetric.GentzenBlockContraction

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

theorem side_ext (o : Op) {X : NormalForm P} {Γ : List (NormalForm P)}
    (f g : (side P o).Hom X (fold o Γ))
    (h : ∀ {A : NormalForm P} (a : At Γ A),
      (side P o).comp f (component o a) = (side P o).comp g (component o a)) : f = g := by
  cases o
  · exact product_positions f g h
  · exact coproduct_positions f g h

namespace Rewire

def dupContext (Γ : List (NormalForm P)) : Rewire P Γ (Γ ++ Γ) :=
  (duplicate [] Γ []).reindex (by simp only [List.nil_append, List.append_nil])
    (by simp only [List.nil_append, List.append_nil])

def dupTail (C : NormalForm P) (Γ : List (NormalForm P)) :
    Rewire P (C :: Γ) (C :: (Γ ++ Γ)) :=
  (duplicate [C] Γ []).reindex (by simp only [List.singleton_append, List.append_nil])
    (by simp only [List.cons_append, List.append_nil, List.nil_append])

theorem dupContext_index (Γ : List (NormalForm P)) {A : NormalForm P} (a : At (Γ ++ Γ) A) :
    ((dupContext Γ).get a).index = duplicateIndex 0 Γ.length a.index := by
  simp only [dupContext, get_index_reindex, duplicate_index, List.length_nil, At.index_cast]

theorem dupTail_index (C : NormalForm P) (Γ : List (NormalForm P))
    {A : NormalForm P} (a : At (C :: (Γ ++ Γ)) A) :
    ((dupTail C Γ).get a).index = duplicateIndex 1 Γ.length a.index := by
  simp only [dupTail, get_index_reindex, duplicate_index, List.length_cons, List.length_nil, At.index_cast]

theorem dupContext_first (Γ : List (NormalForm P)) {A : NormalForm P} (a : At Γ A) :
    (dupContext Γ).get (a.before Γ) = a := by
  apply At.index_injective
  rw [dupContext_index, At.index_before]
  have hi := a.index_lt
  simp only [duplicateIndex, Nat.zero_add, ite_eq_left hi]

theorem dupContext_second (Γ : List (NormalForm P)) {A : NormalForm P} (a : At Γ A) :
    (dupContext Γ).get (At.shift Γ a) = a := by
  apply At.index_injective
  rw [dupContext_index, At.index_shift]
  simp only [duplicateIndex, Nat.zero_add]
  split <;> omega

theorem dupContext_arrow (o : Op) (Γ : List (NormalForm P)) :
    (dupContext Γ).arrow o =
      (side P o).comp ((sideD P o).diag (fold o Γ)) (join o Γ Γ) := by
  let C := side P o
  let M := sideM P o
  let D := sideD P o
  apply side_ext o
  intro A a
  rw [arrow_component]
  cases At.cases_append Γ Γ a with
  | inl h =>
    obtain ⟨b, rfl⟩ := h
    rw [dupContext_first, C.assoc, join_before, ← C.assoc, D.diag_fst, C.id_comp]
  | inr h =>
    obtain ⟨b, rfl⟩ := h
    rw [dupContext_second, C.assoc, join_shift, ← C.assoc, D.diag_snd, C.id_comp]

theorem dupTail_here (C : NormalForm P) (Γ : List (NormalForm P)) :
    (dupTail C Γ).get (.here C (Γ ++ Γ)) = .here C Γ := by
  apply At.index_injective
  rw [dupTail_index]
  change duplicateIndex 1 Γ.length 0 = 0
  simp only [duplicateIndex, Nat.zero_sub, ite_self]

theorem dupTail_first (C : NormalForm P) (Γ : List (NormalForm P))
    {A : NormalForm P} (a : At Γ A) :
    (dupTail C Γ).get (.there (a.before Γ)) = .there a := by
  apply At.index_injective
  rw [dupTail_index]
  simp only [At.index, At.index_before, duplicateIndex]
  have hi := a.index_lt
  split <;> omega

theorem dupTail_second (C : NormalForm P) (Γ : List (NormalForm P))
    {A : NormalForm P} (a : At Γ A) :
    (dupTail C Γ).get (.there (At.shift Γ a)) = .there a := by
  apply At.index_injective
  rw [dupTail_index]
  simp only [At.index, At.index_shift, duplicateIndex]
  split <;> omega

theorem dupTail_arrow (o : Op) (C : NormalForm P) (Γ : List (NormalForm P)) :
    (dupTail C Γ).arrow o = (sideM P o).tensor ((side P o).id C)
      ((side P o).comp ((sideD P o).diag (fold o Γ)) (join o Γ Γ)) := by
  let K := side P o
  let M := sideM P o
  let D := sideD P o
  apply side_ext o
  intro A a
  rw [arrow_component]
  cases a with
  | here =>
    rw [dupTail_here]
    simp only [component_here]
    rw [← D.fst_nat, K.comp_id]
  | there a =>
    rw [component_there, ← K.assoc, ← D.snd_nat, K.assoc]
    cases At.cases_append Γ Γ a with
    | inl h =>
      obtain ⟨b, rfl⟩ := h
      rw [dupTail_first, K.assoc, join_before, component_there]
      change K.comp (D.snd C (fold o Γ)) (component o b) =
        K.comp (D.snd C (fold o Γ))
          (K.comp (D.diag (fold o Γ)) (K.comp (D.fst (fold o Γ) (fold o Γ)) (component o b)))
      rw [← K.assoc (D.diag (fold o Γ)), D.diag_fst, K.id_comp]
    | inr h =>
      obtain ⟨b, rfl⟩ := h
      rw [dupTail_second, K.assoc, join_shift, component_there]
      change K.comp (D.snd C (fold o Γ)) (component o b) =
        K.comp (D.snd C (fold o Γ))
          (K.comp (D.diag (fold o Γ)) (K.comp (D.snd (fold o Γ) (fold o Γ)) (component o b)))
      rw [← K.assoc (D.diag (fold o Γ)), D.diag_snd, K.id_comp]

end Rewire
end DosenPetric.Reduced.Gentzen
