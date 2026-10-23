module

public import DosenPetric.GentzenProofOccurrences

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

namespace Premise

/-- Independent upper-to-lower rule routing. Consumed or newly introduced
    logical components have no whole-formula descendant at this rule. -/
def parent {Γ Δ Θ Λ : List (NormalForm P)} {f : G P Γ Δ} {g : G P Θ Λ}
    (p : Premise f g) (s : SequentSide) :
    {C : NormalForm P} → Place s Θ Λ C → Option (Place s Γ Δ C) :=
  match p,s with
  | .exchangeL Γ X Y Θ _ _, .left => fun a => some (a.swapBlocks Γ X Y Θ)
  | .exchangeL .., .right => fun a => some a
  | .exchangeR .., .left => fun a => some a
  | .exchangeR _ Δ X Y Λ _, .right => fun a => some (a.swapBlocks Δ X Y Λ)
  | .thinL Γ Θ _ A _, .left => fun a => some ((Route.thin Γ Θ A).get a)
  | .thinL .., .right => fun a => some a
  | .thinR .., .left => fun a => some a
  | .thinR _ Δ Λ A _, .right => fun a => some ((Route.thin Δ Λ A).get a)
  | .contractL C gs Θ _ _ _, .left => fun a => some ((copies C gs Θ).get a)
  | .contractL .., .right => fun a => some a
  | .contractR .., .left => fun a => some a
  | .contractR _ C gs Λ _ _, .right => fun a => some ((copies C gs Λ).get a)
  | .conjL Γ Θ _ A B _, .left => At.fixed Γ [A,B] [.conj A B] Θ
  | .conjL .., .right => fun a => some a
  | .disjR .., .left => fun a => some a
  | .disjR _ Δ Λ A B _, .right => At.fixed Δ [A,B] [.disj A B] Λ
  | @conjR_left _ Γ Θ _ _ _ _ _ _, .left => fun a => some (a.before Θ)
  | @conjR_right _ Γ _ _ _ _ _ _ _, .left => fun a => some (At.shift Γ a)
  | @conjR_left _ _ _ _ Λ A B _ _, .right => fun
    | .here _ _ => none
    | .there a => some (.there (a.before Λ))
  | @conjR_right _ _ _ Δ _ A B _ _, .right => fun
    | .here _ _ => none
    | .there a => some (.there (At.shift Δ a))
  | @disjL_left _ _ Θ _ _ A B _ _, .left => fun
    | .here _ _ => none
    | .there a => some (.there (a.before Θ))
  | @disjL_right _ Γ _ _ _ A B _ _, .left => fun
    | .here _ _ => none
    | .there a => some (.there (At.shift Γ a))
  | @disjL_left _ _ _ _ Λ _ _ _ _, .right => fun a => some (a.before Λ)
  | @disjL_right _ _ _ Δ _ _ _ _ _, .right => fun a => some (At.shift Δ a)
  | @mix_left _ _ Θ _ Λ _ _, .left => fun a => some (At.shift Θ a)
  | @mix_left _ _ Θ _ Λ _ _, .right => fun a => some (At.shift Λ a)
  | @mix_right _ Γ _ Δ _ _ _, .left => fun a => some (a.before Γ)
  | @mix_right _ Γ _ Δ _ _ _, .right => fun a => some (a.before Δ)
  | @cut_left _ _ Θ _ _ _ _ _, .left => fun a => some (At.shift Θ a)
  | @cut_left _ _ _ _ Λ _ _ _, .right => fun
    | .here _ _ => none
    | .there a => some (At.shift Λ a)
  | @cut_right _ Γ _ _ _ _ _ _, .left => fun
    | .here _ _ => none
    | .there a => some (a.before Γ)
  | @cut_right _ _ _ Δ _ _ _ _, .right => fun a => some (a.before Δ)

def route {Γ Δ Θ Λ : List (NormalForm P)} {f : G P Γ Δ} {g : G P Θ Λ}
    (p : Premise f g) (s : SequentSide) : TraceRoute (s.context Γ Δ) (s.context Θ Λ) :=
  TraceRoute.ofMap _ _ (p.parent s)

theorem route_correct {Γ Δ Θ Λ : List (NormalForm P)} {f : G P Γ Δ} {g : G P Θ Λ}
    (p : Premise f g) (s : SequentSide) {C : NormalForm P} (a : Place s Θ Λ C) :
    (p.route s).get a = p.parent s a := TraceRoute.get_ofMap ..

end Premise

structure Branch {Γ Δ : List (NormalForm P)} (g : G P Γ Δ) where
  source : List (NormalForm P)
  target : List (NormalForm P)
  proof : G P source target
  occurrence : Premise g proof

namespace G

def branches : {Γ Δ : List (NormalForm P)} → (g : G P Γ Δ) → List (Branch g)
  | _,_, .identity _ | _,_, .zero _ | _,_, .topI | _,_, .botE => []
  | _,_, .exchangeL Γ X Y Θ Δ f => [⟨_,_,f,.exchangeL Γ X Y Θ Δ f⟩]
  | _,_, .exchangeR Γ Δ X Y Λ f => [⟨_,_,f,.exchangeR Γ Δ X Y Λ f⟩]
  | _,_, .thinL Γ Θ Δ A f => [⟨_,_,f,.thinL Γ Θ Δ A f⟩]
  | _,_, .thinR Γ Δ Λ A f => [⟨_,_,f,.thinR Γ Δ Λ A f⟩]
  | _,_, .contractL C gs Θ Δ hn f => [⟨_,_,f,.contractL C gs Θ Δ hn f⟩]
  | _,_, .contractR Γ C gs Λ hn f => [⟨_,_,f,.contractR Γ C gs Λ hn f⟩]
  | _,_, .conjL Γ Θ Δ A B f => [⟨_,_,f,.conjL Γ Θ Δ A B f⟩]
  | _,_, .disjR Γ Δ Λ A B f => [⟨_,_,f,.disjR Γ Δ Λ A B f⟩]
  | _,_, .conjR f g => [⟨_,_,f,.conjR_left f g⟩,⟨_,_,g,.conjR_right f g⟩]
  | _,_, .disjL f g => [⟨_,_,f,.disjL_left f g⟩,⟨_,_,g,.disjL_right f g⟩]
  | _,_, .mix f g => [⟨_,_,f,.mix_left f g⟩,⟨_,_,g,.mix_right f g⟩]
  | _,_, .cut f g => [⟨_,_,f,.cut_left f g⟩,⟨_,_,g,.cut_right f g⟩]

theorem branches_complete {Γ Δ : List (NormalForm P)} {g : G P Γ Δ} (b : Branch g) :
    b ∈ g.branches := by
  obtain ⟨_,_,_,p⟩ := b
  cases p <;> simp [branches]

end G

structure Upper {Γ Δ : List (NormalForm P)} (g : G P Γ Δ) (s : SequentSide) (C : NormalForm P) where
  branch : Branch g
  position : Place s branch.source branch.target C

namespace G

def predecessors {Γ Δ : List (NormalForm P)} (g : G P Γ Δ) (s : SequentSide)
    {C : NormalForm P} (x : Place s Γ Δ C) : List (Upper g s C) :=
  g.branches.flatMap fun b => ((b.occurrence.route s).fiber x).map (fun y => ⟨b,y⟩)

/-- This specification is the independent upper-to-lower rule map. -/
def IsPredecessor {Γ Δ : List (NormalForm P)} (g : G P Γ Δ) (s : SequentSide)
    {C : NormalForm P} (x : Place s Γ Δ C) (u : Upper g s C) : Prop :=
  u.branch.occurrence.parent s u.position = some x

theorem predecessors_correct {Γ Δ : List (NormalForm P)} (g : G P Γ Δ) (s : SequentSide)
    {C : NormalForm P} (x : Place s Γ Δ C) (u : Upper g s C) :
    u ∈ g.predecessors s x ↔ g.IsPredecessor s x u := by
  simp only [predecessors, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨b,_,y,hy,he⟩
    cases he
    exact (b.occurrence.route_correct s y).symm.trans ((TraceRoute.fiber_correct _ _ _).mp hy)
  · intro h
    refine ⟨u.branch,branches_complete _,u.position,?_,rfl⟩
    apply (TraceRoute.fiber_correct _ _ _).mpr
    exact (u.branch.occurrence.route_correct s u.position).trans h

theorem predecessor_proofSize_lt {Γ Δ : List (NormalForm P)} (g : G P Γ Δ) (s : SequentSide)
    {C : NormalForm P} (u : Upper g s C) : u.branch.proof.proofSize < g.proofSize :=
  u.branch.occurrence.proofSize_lt

end G
end DosenPetric.Reduced.Gentzen
