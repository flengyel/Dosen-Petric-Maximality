module

public import DosenPetric.GentzenBlockedSource

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
open BlockedSource

/-- The seven displayed source left patterns, with actual selected gaps.
    Terminal logical order is realized by explicit proof constructors. -/
inductive BlockedL {P : Type u} : {Γ Δ : List (NormalForm P)} → G P Γ Δ → Prop where
  | gammaMix (C : NormalForm P) (X Y Z T Δ Λ : List (NormalForm P))
      (f : G P (X++C::Y) Δ) (g : G P (Z++C::T) Λ) :
      BlockedL (left2 C Z (T++X) Y (Λ++Δ) ((G.mix f g).reindex (by simp only [List.append_assoc,List.cons_append]) rfl))
  | gammaConj (C A B : NormalForm P) (X Y Z T Δ Λ : List (NormalForm P))
      (f : G P (X++C::Y) (A::Δ)) (g : G P (Z++C::T) (B::Λ)) :
      BlockedL (left2 C X (Y++Z) T (.conj A B::(Δ++Λ)) ((G.conjR f g).reindex (by simp only [List.append_assoc,List.cons_append]) rfl))
  | gammaDisj (C A B : NormalForm P) (X Y Z T Δ Λ : List (NormalForm P))
      (f : G P ((X++C::Y)++[A]) Δ) (g : G P ((Z++C::T)++[B]) Λ) :
      BlockedL (left2 C X (Y++Z) (T++[.disj A B]) (Δ++Λ) ((disjLLast f g).reindex (by simp only [List.append_assoc,List.cons_append]) rfl))
  | conjunction (A B : NormalForm P) (X Y Δ : List (NormalForm P))
      (f : G P ((X++.conj A B::Y)++[A,B]) Δ) :
      BlockedL (left2 (.conj A B) X Y [] Δ ((conjLLast (X++.conj A B::Y) Δ A B f).reindex (by simp only [List.append_assoc,List.cons_append]) rfl))
  | disjunctionFirst (A B : NormalForm P) (X Y Z Δ Λ : List (NormalForm P))
      (f : G P ((X++.disj A B::Y)++[A]) Δ) (g : G P (Z++[B]) Λ) :
      BlockedL (left2 (.disj A B) X (Y++Z) [] (Δ++Λ) ((disjLLast f g).reindex (by simp only [List.append_assoc,List.cons_append]) rfl))
  | disjunctionSecond (A B : NormalForm P) (X Z T Δ Λ : List (NormalForm P))
      (f : G P (X++[A]) Δ) (g : G P ((Z++.disj A B::T)++[B]) Λ) :
      BlockedL (left2 (.disj A B) (X++Z) T [] (Δ++Λ) ((disjLLast f g).reindex (by simp only [List.append_assoc,List.cons_append]) rfl))
  | disjunctionBoth (A B : NormalForm P) (X Y Z T Δ Λ : List (NormalForm P))
      (f : G P ((X++.disj A B::Y)++[A]) Δ) (g : G P ((Z++.disj A B::T)++[B]) Λ) :
      BlockedL (left3 (.disj A B) X (Y++Z) T [] (Δ++Λ) ((disjLLast f g).reindex (by simp only [List.append_assoc,List.cons_append]) rfl))

/-- Separately typed right-dual patterns for the primitive last-retaining
    contraction. The source first-retaining order uses contractRFirst. -/
inductive BlockedR {P : Type u} : {Γ Δ : List (NormalForm P)} → G P Γ Δ → Prop where
  | gammaMix (C : NormalForm P) (Γ Θ X Y Z T : List (NormalForm P))
      (f : G P Γ (X++C::Y)) (g : G P Θ (Z++C::T)) :
      BlockedR (right2 C (Θ++Γ) Z (T++X) Y ((G.mix f g).reindex rfl (by simp only [List.append_assoc,List.cons_append])))
  | gammaDisj (C A B : NormalForm P) (Γ Θ X Y Z T : List (NormalForm P))
      (f : G P (Γ++[A]) (X++C::Y)) (g : G P (Θ++[B]) (Z++C::T)) :
      BlockedR (right2 C ((Γ++Θ)++[.disj A B]) X (Y++Z) T ((disjLLast f g).reindex rfl (by simp only [List.append_assoc,List.cons_append])))
  | gammaConj (C A B : NormalForm P) (Γ Θ X Y Z T : List (NormalForm P))
      (f : G P Γ (A::(X++C::Y))) (g : G P Θ (B::(Z++C::T))) :
      BlockedR (right2 C (Γ++Θ) (.conj A B::X) (Y++Z) T ((G.conjR f g).reindex rfl (by simp only [List.append_assoc,List.cons_append])))
  | disjunction (A B : NormalForm P) (Γ X Y : List (NormalForm P))
      (f : G P Γ (A::B::(X++.disj A B::Y))) :
      BlockedR (right2 (.disj A B) Γ [] X Y (G.disjR Γ [] (X++.disj A B::Y) A B f))
  | conjunctionFirst (A B : NormalForm P) (Γ Θ X Y Λ : List (NormalForm P))
      (f : G P Γ (A::(X++.conj A B::Y))) (g : G P Θ (B::Λ)) :
      BlockedR (right2 (.conj A B) (Γ++Θ) [] X (Y++Λ) ((G.conjR f g).reindex rfl (by simp only [List.nil_append,List.append_assoc,List.cons_append])))
  | conjunctionSecond (A B : NormalForm P) (Γ Θ Δ Z T : List (NormalForm P))
      (f : G P Γ (A::Δ)) (g : G P Θ (B::(Z++.conj A B::T))) :
      BlockedR (right2 (.conj A B) (Γ++Θ) [] (Δ++Z) T ((G.conjR f g).reindex rfl (by simp only [List.nil_append,List.append_assoc])))
  | conjunctionBoth (A B : NormalForm P) (Γ Θ X Y Z T : List (NormalForm P))
      (f : G P Γ (A::(X++.conj A B::Y))) (g : G P Θ (B::(Z++.conj A B::T))) :
      BlockedR (right3 (.conj A B) (Γ++Θ) [] X (Y++Z) T ((G.conjR f g).reindex rfl (by simp only [List.nil_append,List.append_assoc,List.cons_append])))

namespace BlockedL
variable {P : Type u} {Γ Δ : List (NormalForm P)} {g : G P Γ Δ}
theorem lower (h : BlockedL g) : ∃ (C : NormalForm P) (x : At Γ C), G.LowerContraction g .left x := by
  cases h <;> exact ⟨_,_,G.LowerContraction.left ..⟩
end BlockedL
namespace BlockedR
variable {P : Type u} {Γ Δ : List (NormalForm P)} {g : G P Γ Δ}
theorem lower (h : BlockedR g) : ∃ (C : NormalForm P) (x : At Δ C), G.LowerContraction g .right x := by
  cases h <;> exact ⟨_,_,G.LowerContraction.right ..⟩
end BlockedR

end DosenPetric.Reduced.Gentzen
