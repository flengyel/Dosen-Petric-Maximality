module

public import DosenPetric.GentzenUnaryFibers

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

namespace TraceRoute

theorem partition_length (Γ Θ : List (NormalForm P)) {C : NormalForm P} (x : At (Γ ++ Θ) C) :
    ((before Γ Θ).fiber x).length + ((shift Γ Θ).fiber x).length = 1 := by
  rw [fiber_before,fiber_shift]
  cases At.splitAppend Γ Θ x <;> rfl

theorem wrap_partition_length (Γ Θ : List (NormalForm P)) (H A B : NormalForm P)
    {C : NormalForm P} (x : At (H :: (Γ ++ Θ)) C) :
    ((wrap H A (before Γ Θ)).fiber x).length + ((wrap H B (shift Γ Θ)).fiber x).length =
      if x.index = 0 then 0 else 1 := by
  cases x with
  | here => rw [fiber_wrap_here,fiber_wrap_here]; rfl
  | there x =>
    rw [fiber_wrap_there,fiber_wrap_there,List.length_map,List.length_map,partition_length]
    simp only [At.index,Nat.add_one_ne_zero,ite_false]

end TraceRoute

namespace Premise

theorem conjR_left_right_route {Γ Θ Δ Λ : List (NormalForm P)} {A B : NormalForm P}
    (f : G P Γ (A :: Δ)) (g : G P Θ (B :: Λ)) :
    (Premise.conjR_left f g).route .right = TraceRoute.wrap (.conj A B) A (TraceRoute.before Δ Λ) := by
  apply TraceRoute.ext
  intro C a
  rw [route_correct (Premise.conjR_left f g) .right a]
  cases a with
  | here => rfl
  | there a =>
    change some (a.before Λ).there = (TraceRoute.ofMap _ Δ (fun z => ((TraceRoute.before Δ Λ).get z).map At.there)).get a
    rw [TraceRoute.get_ofMap _ Δ _ a]
    exact (congrArg (Option.map (@At.there P C (.conj A B) (Δ ++ Λ)))
      (TraceRoute.get_ofMap (Δ ++ Λ) Δ (fun z => some (z.before Λ)) a)).symm

theorem conjR_right_right_route {Γ Θ Δ Λ : List (NormalForm P)} {A B : NormalForm P}
    (f : G P Γ (A :: Δ)) (g : G P Θ (B :: Λ)) :
    (Premise.conjR_right f g).route .right = TraceRoute.wrap (.conj A B) B (TraceRoute.shift Δ Λ) := by
  apply TraceRoute.ext
  intro C a
  rw [route_correct (Premise.conjR_right f g) .right a]
  cases a with
  | here => rfl
  | there a =>
    change some (At.shift Δ a).there = (TraceRoute.ofMap _ Λ (fun z => ((TraceRoute.shift Δ Λ).get z).map At.there)).get a
    rw [TraceRoute.get_ofMap _ Λ _ a]
    exact (congrArg (Option.map (@At.there P C (.conj A B) (Δ ++ Λ)))
      (TraceRoute.get_ofMap (Δ ++ Λ) Λ (fun z => some (At.shift Δ z)) a)).symm

theorem disjL_left_left_route {Γ Θ Δ Λ : List (NormalForm P)} {A B : NormalForm P}
    (f : G P (A :: Γ) Δ) (g : G P (B :: Θ) Λ) :
    (Premise.disjL_left f g).route .left = TraceRoute.wrap (.disj A B) A (TraceRoute.before Γ Θ) := by
  apply TraceRoute.ext
  intro C a
  rw [route_correct (Premise.disjL_left f g) .left a]
  cases a with
  | here => rfl
  | there a =>
    change some (a.before Θ).there = (TraceRoute.ofMap _ Γ (fun z => ((TraceRoute.before Γ Θ).get z).map At.there)).get a
    rw [TraceRoute.get_ofMap _ Γ _ a]
    exact (congrArg (Option.map (@At.there P C (.disj A B) (Γ ++ Θ)))
      (TraceRoute.get_ofMap (Γ ++ Θ) Γ (fun z => some (z.before Θ)) a)).symm

theorem disjL_right_left_route {Γ Θ Δ Λ : List (NormalForm P)} {A B : NormalForm P}
    (f : G P (A :: Γ) Δ) (g : G P (B :: Θ) Λ) :
    (Premise.disjL_right f g).route .left = TraceRoute.wrap (.disj A B) B (TraceRoute.shift Γ Θ) := by
  apply TraceRoute.ext
  intro C a
  rw [route_correct (Premise.disjL_right f g) .left a]
  cases a with
  | here => rfl
  | there a =>
    change some (At.shift Γ a).there = (TraceRoute.ofMap _ Θ (fun z => ((TraceRoute.shift Γ Θ).get z).map At.there)).get a
    rw [TraceRoute.get_ofMap _ Θ _ a]
    exact (congrArg (Option.map (@At.there P C (.disj A B) (Γ ++ Θ)))
      (TraceRoute.get_ofMap (Γ ++ Θ) Θ (fun z => some (At.shift Γ z)) a)).symm

theorem cut_left_right_route {Γ Θ Δ Λ : List (NormalForm P)} {C : NormalForm P}
    (f : G P Γ (C :: Δ)) (g : G P (C :: Θ) Λ) :
    (Premise.cut_left f g).route .right = TraceRoute.cons none (TraceRoute.shift Λ Δ) := by
  apply TraceRoute.ext
  intro A a
  rw [route_correct (Premise.cut_left f g) .right a]
  cases a with
  | here => rfl
  | there a => exact (TraceRoute.get_ofMap (Λ ++ Δ) Δ (fun z => some (At.shift Λ z)) a).symm

theorem cut_right_left_route {Γ Θ Δ Λ : List (NormalForm P)} {C : NormalForm P}
    (f : G P Γ (C :: Δ)) (g : G P (C :: Θ) Λ) :
    (Premise.cut_right f g).route .left = TraceRoute.cons none (TraceRoute.before Θ Γ) := by
  apply TraceRoute.ext
  intro A a
  rw [route_correct (Premise.cut_right f g) .left a]
  cases a with
  | here => rfl
  | there a => exact (TraceRoute.get_ofMap (Θ ++ Γ) Θ (fun z => some (z.before Γ)) a).symm

end Premise
end DosenPetric.Reduced.Gentzen
