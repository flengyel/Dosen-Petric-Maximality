module

public import DosenPetric.GentzenBinaryFibers

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

namespace G

/-- Source rule classification, defined from rule and selected conclusion
    index independently of predecessor enumeration. Zero denotes a leaf,
    one a parametric position, and n≥2 a lower n-fold contraction position. -/
def sourceArity : {Γ Δ : List (NormalForm P)} → (g : G P Γ Δ) →
    (s : SequentSide) → {C : NormalForm P} → Place s Γ Δ C → Nat
  | _,_, .identity _, _,_,_ | _,_, .zero _, _,_,_
  | _,_, .topI, _,_,_ | _,_, .botE, _,_,_ => 0
  | _,_, .thinL Γ _ _ _ _, .left,_,x => if x.index = Γ.length then 0 else 1
  | _,_, .thinR _ Δ _ _ _, .right,_,x => if x.index = Δ.length then 0 else 1
  | _,_, .contractL _ gs _ _ _ _, .left,_,x => if x.index = (gaps gs).length then gs.length else 1
  | _,_, .contractR _ _ gs _ _ _, .right,_,x => if x.index = (gaps gs).length then gs.length else 1
  | _,_, .conjL Γ _ _ _ _ _, .left,_,x => if x.index = Γ.length then 0 else 1
  | _,_, .disjR _ Δ _ _ _ _, .right,_,x => if x.index = Δ.length then 0 else 1
  | _,_, .conjR _ _, .right,_,x | _,_, .disjL _ _, .left,_,x => if x.index = 0 then 0 else 1
  | _,_, _, _,_,_ => 1

def Leaf {Γ Δ : List (NormalForm P)} (g : G P Γ Δ) (s : SequentSide)
    {C : NormalForm P} (x : Place s Γ Δ C) : Prop := g.sourceArity s x = 0

def Parametric {Γ Δ : List (NormalForm P)} (g : G P Γ Δ) (s : SequentSide)
    {C : NormalForm P} (x : Place s Γ Δ C) : Prop := g.sourceArity s x = 1

theorem predecessors_length {Γ Δ : List (NormalForm P)} (g : G P Γ Δ) (s : SequentSide)
    {C : NormalForm P} (x : Place s Γ Δ C) :
    (g.predecessors s x).length = (g.branches.map (fun b => ((b.occurrence.route s).fiber x).length)).sum := by
  simp only [predecessors,List.length_flatMap,List.length_map]

/-- Exact agreement between source rule classification and computed data. -/
theorem sourceArity_correct {Γ Δ : List (NormalForm P)} (g : G P Γ Δ) (s : SequentSide)
    {C : NormalForm P} (x : Place s Γ Δ C) : (g.predecessors s x).length = g.sourceArity s x := by
  rw [predecessors_length]
  cases g with
  | identity => cases s <;> rfl
  | zero => cases s <;> rfl
  | topI => cases s <;> rfl
  | botE => cases s <;> rfl
  | exchangeL Γ X Y Θ Δ f =>
    cases s
    · change ((TraceRoute.ofMap _ _ (fun a => some (a.swapBlocks Γ X Y Θ))).fiber x).length + 0 = 1
      exact congrArg (fun ys => ys.length + 0) (fiber_swap _ _ _ _ x)
    · change ((TraceRoute.ofMap Δ Δ (fun a => some a)).fiber x).length + 0 = 1
      exact congrArg (fun ys => ys.length + 0) (TraceRoute.fiber_identity _ x)
  | exchangeR Γ Δ X Y Λ f =>
    cases s
    · change ((TraceRoute.ofMap Γ Γ (fun a => some a)).fiber x).length + 0 = 1
      exact congrArg (fun ys => ys.length + 0) (TraceRoute.fiber_identity _ x)
    · change ((TraceRoute.ofMap _ _ (fun a => some (a.swapBlocks Δ X Y Λ))).fiber x).length + 0 = 1
      exact congrArg (fun ys => ys.length + 0) (fiber_swap _ _ _ _ x)
  | thinL Γ Θ Δ A f =>
    cases s
    · change ((TraceRoute.full (Route.thin Γ Θ A)).fiber x).length + 0 = if x.index = Γ.length then 0 else 1
      exact (Nat.add_zero _).trans (fiber_thin_length Γ Θ A x)
    · change ((TraceRoute.ofMap Δ Δ (fun a => some a)).fiber x).length + 0 = 1
      exact congrArg (fun ys => ys.length + 0) (TraceRoute.fiber_identity _ x)
  | thinR Γ Δ Λ A f =>
    cases s
    · change ((TraceRoute.ofMap Γ Γ (fun a => some a)).fiber x).length + 0 = 1
      exact congrArg (fun ys => ys.length + 0) (TraceRoute.fiber_identity _ x)
    · change ((TraceRoute.full (Route.thin Δ Λ A)).fiber x).length + 0 = if x.index = Δ.length then 0 else 1
      exact (Nat.add_zero _).trans (fiber_thin_length Δ Λ A x)
  | contractL A gs Θ Δ hn f =>
    cases s
    · change ((TraceRoute.full (copies A gs Θ)).fiber x).length + 0 = if x.index = (gaps gs).length then gs.length else 1
      exact (Nat.add_zero _).trans (fiber_copies_length A gs Θ x)
    · change ((TraceRoute.ofMap Δ Δ (fun a => some a)).fiber x).length + 0 = 1
      exact congrArg (fun ys => ys.length + 0) (TraceRoute.fiber_identity _ x)
  | contractR Γ A gs Λ hn f =>
    cases s
    · change ((TraceRoute.ofMap Γ Γ (fun a => some a)).fiber x).length + 0 = 1
      exact congrArg (fun ys => ys.length + 0) (TraceRoute.fiber_identity _ x)
    · change ((TraceRoute.full (copies A gs Λ)).fiber x).length + 0 = if x.index = (gaps gs).length then gs.length else 1
      exact (Nat.add_zero _).trans (fiber_copies_length A gs Λ x)
  | conjL Γ Θ Δ A B f =>
    cases s
    · change ((TraceRoute.ofMap _ _ (At.fixed Γ [A,B] [.conj A B] Θ)).fiber x).length + 0 = if x.index = Γ.length then 0 else 1
      exact (Nat.add_zero _).trans (fiber_logical_length Γ Θ (.conj A B) [A,B] x)
    · change ((TraceRoute.ofMap Δ Δ (fun a => some a)).fiber x).length + 0 = 1
      exact congrArg (fun ys => ys.length + 0) (TraceRoute.fiber_identity _ x)
  | disjR Γ Δ Λ A B f =>
    cases s
    · change ((TraceRoute.ofMap Γ Γ (fun a => some a)).fiber x).length + 0 = 1
      exact congrArg (fun ys => ys.length + 0) (TraceRoute.fiber_identity _ x)
    · change ((TraceRoute.ofMap _ _ (At.fixed Δ [A,B] [.disj A B] Λ)).fiber x).length + 0 = if x.index = Δ.length then 0 else 1
      exact (Nat.add_zero _).trans (fiber_logical_length Δ Λ (.disj A B) [A,B] x)
  | @conjR Γ Θ Δ Λ A B f g =>
    simp only [branches,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero]
    cases s
    · exact TraceRoute.partition_length Γ Θ x
    · rw [Premise.conjR_left_right_route,Premise.conjR_right_right_route]
      exact TraceRoute.wrap_partition_length Δ Λ (.conj A B) A B x
  | @disjL Γ Θ Δ Λ A B f g =>
    simp only [branches,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero]
    cases s
    · rw [Premise.disjL_left_left_route,Premise.disjL_right_left_route]
      exact TraceRoute.wrap_partition_length Γ Θ (.disj A B) A B x
    · exact TraceRoute.partition_length Δ Λ x
  | @mix Γ Θ Δ Λ f g =>
    simp only [branches,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero]
    cases s
    · exact (Nat.add_comm _ _).trans (TraceRoute.partition_length Θ Γ x)
    · exact (Nat.add_comm _ _).trans (TraceRoute.partition_length Λ Δ x)
  | @cut Γ Θ Δ Λ A f g =>
    simp only [branches,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero]
    cases s
    · change At (Θ ++ Γ) C at x
      rw [Premise.cut_right_left_route]
      change ((TraceRoute.shift Θ Γ).fiber x).length +
        (((TraceRoute.before Θ Γ).fiber x).map (@At.there P C A Θ)).length = 1
      rw [List.length_map]
      exact (Nat.add_comm _ _).trans (TraceRoute.partition_length Θ Γ x)
    · change At (Λ ++ Δ) C at x
      rw [Premise.cut_left_right_route]
      change (((TraceRoute.shift Λ Δ).fiber x).map (@At.there P C A Δ)).length +
        ((TraceRoute.before Λ Δ).fiber x).length = 1
      rw [List.length_map]
      exact (Nat.add_comm _ _).trans (TraceRoute.partition_length Λ Δ x)

theorem leaf_iff_no_predecessor {Γ Δ : List (NormalForm P)} (g : G P Γ Δ) (s : SequentSide)
    {C : NormalForm P} (x : Place s Γ Δ C) :
    g.Leaf s x ↔ ∀ a : Upper g s C, ¬ g.IsPredecessor s x a := by
  rw [Leaf,← sourceArity_correct,List.length_eq_zero_iff,List.eq_nil_iff_forall_not_mem]
  constructor
  · intro h a ha; exact h a ((g.predecessors_correct s x a).mpr ha)
  · intro h a ha; exact h a ((g.predecessors_correct s x a).mp ha)

theorem parametric_unique {Γ Δ : List (NormalForm P)} (g : G P Γ Δ) (s : SequentSide)
    {C : NormalForm P} (x : Place s Γ Δ C) (h : g.Parametric s x) :
    ∃ a : Upper g s C, g.predecessors s x = [a] ∧
      ∀ b : Upper g s C, g.IsPredecessor s x b ↔ b = a := by
  have hl : (g.predecessors s x).length = 1 := (g.sourceArity_correct s x).trans h
  obtain ⟨a,ha⟩ := List.length_eq_one_iff.mp hl
  refine ⟨a,ha,?_⟩
  intro b
  rw [← g.predecessors_correct s x b,ha]
  simp

end G
end DosenPetric.Reduced.Gentzen
