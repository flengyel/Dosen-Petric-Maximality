module

public import DosenPetric.GentzenLinearFibers
public import DosenPetric.GentzenCopyFibers
public import DosenPetric.GentzenPredecessors

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

theorem thin_parent_fixed (Γ Θ : List (NormalForm P)) (A : NormalForm P)
    {C : NormalForm P} (x : At (Γ ++ Θ) C) :
    some ((Route.thin Γ Θ A).get x) = At.fixed Γ [] [A] Θ x := by
  induction Γ with
  | nil => simp only [Route.thin,Route.get_map,Route.get_identity,At.fixed,At.splitAppend,At.shift]
  | cons B Γ ih =>
    cases x with
    | here => rfl
    | there x =>
      simp only [Route.thin,Route.get,Route.get_map,At.fixed]
      exact (congrArg (Option.map At.there) (ih x))

theorem exchangeIndex_inverse (g x y i : Nat) :
    exchangeIndex g y x (exchangeIndex g x y i) = i := by
  simp only [exchangeIndex]
  repeat first | split | omega

theorem swapBlocks_inverse (Γ X Y Θ : List (NormalForm P)) {C : NormalForm P}
    (a : At (Γ ++ X ++ Y ++ Θ) C) :
    (a.swapBlocks Γ X Y Θ).swapBlocks Γ Y X Θ = a := by
  apply At.index_injective
  rw [swapBlocks_index,swapBlocks_index,exchangeIndex_inverse]

theorem fiber_swap (Γ X Y Θ : List (NormalForm P)) {C : NormalForm P}
    (x : At (Γ ++ Y ++ X ++ Θ) C) :
    (TraceRoute.ofMap _ _ (fun a => some (a.swapBlocks Γ X Y Θ))).fiber x =
      [x.swapBlocks Γ Y X Θ] := by
  apply TraceRoute.fiber_single
  intro a
  rw [TraceRoute.get_ofMap,Option.some.injEq]
  constructor
  · intro h
    have hh := congrArg (fun a : At (Γ ++ Y ++ X ++ Θ) C => a.swapBlocks Γ Y X Θ) h
    rwa [swapBlocks_inverse] at hh
  · intro h; cases h; exact swapBlocks_inverse Γ Y X Θ x

theorem fixed_single_length (Γ Θ Y : List (NormalForm P)) (A : NormalForm P)
    {C : NormalForm P} (x : At (Γ ++ A :: Θ) C) :
    (At.fixed Γ [A] Y Θ x).toList.length = if x.index = Γ.length then 0 else 1 := by
  have hn := At.fixed_single_none Γ Θ Y A x
  cases h : At.fixed Γ [A] Y Θ x with
  | none => rw [h] at hn; simp only [Option.toList_none,List.length_nil,ite_eq_left (hn.mp rfl)]
  | some y =>
    have hi : x.index ≠ Γ.length := by intro hi; have hh := hn.mpr hi; rw [h] at hh; cases hh
    simp only [Option.toList_some,List.length_cons,List.length_nil,ite_eq_right hi]

theorem fiber_thin_length (Γ Θ : List (NormalForm P)) (A : NormalForm P)
    {C : NormalForm P} (x : At (Γ ++ A :: Θ) C) :
    ((TraceRoute.full (Route.thin Γ Θ A)).fiber x).length = if x.index = Γ.length then 0 else 1 := by
  have he : TraceRoute.full (Route.thin Γ Θ A) = TraceRoute.ofMap _ _ (At.fixed Γ [] [A] Θ) := by
    apply TraceRoute.ext
    intro C a
    rw [TraceRoute.get_full]
    exact (thin_parent_fixed Γ Θ A a).trans (TraceRoute.get_ofMap _ _ _ a).symm
  rw [he]
  exact (congrArg List.length (TraceRoute.fiber_fixed Γ [] [A] Θ x)).trans (fixed_single_length Γ Θ [] A x)

theorem fiber_logical_length (Γ Θ : List (NormalForm P)) (A : NormalForm P)
    (X : List (NormalForm P)) {C : NormalForm P} (x : At (Γ ++ A :: Θ) C) :
    ((TraceRoute.ofMap _ _ (At.fixed Γ X [A] Θ)).fiber x).length = if x.index = Γ.length then 0 else 1 := by
  exact (congrArg List.length (TraceRoute.fiber_fixed Γ X [A] Θ x)).trans (fixed_single_length Γ Θ X A x)

theorem fiber_copies_length (A : NormalForm P) (gs : List (List (NormalForm P)))
    (Θ : List (NormalForm P)) {C : NormalForm P} (x : At (gaps gs ++ A :: Θ) C) :
    ((TraceRoute.full (copies A gs Θ)).fiber x).length =
      if x.index = (gaps gs).length then gs.length else 1 := by
  by_cases hi : x.index = (gaps gs).length
  · cases h : At.compare x (At.shift (gaps gs) (.here A Θ)) with
    | same => rw [fiber_copies_selected,selectedCopies_length,ite_eq_left hi]
    | apart hn =>
      have he : x.index = (At.shift (gaps gs) (.here A Θ)).index := by
        simpa only [At.index_shift,At.index,Nat.add_zero] using hi
      exact False.elim (hn he)
  · rw [fiber_copies_fixed A gs Θ x hi,ite_eq_right hi]
    rfl

end DosenPetric.Reduced.Gentzen
