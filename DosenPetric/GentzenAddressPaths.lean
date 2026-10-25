module

public import DosenPetric.GentzenAddressTracing

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

namespace Branch
theorem eq_of_branch {Γ Δ : List (NormalForm P)} {g : G P Γ Δ}
    (a b : Branch g) (h : a.occurrence.branch = b.occurrence.branch) : a = b := by
  have ha := G.branches_complete a
  have hb := G.branches_complete b
  cases g <;> simp only [G.branches,List.mem_cons,List.not_mem_nil,or_false] at ha hb
  all_goals first
    | exact False.elim ha
    | exact ha.trans hb.symm
    | (rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp_all [Premise.branch])
end Branch

/-- The same proof occurrences read from the root toward the selected subproof. -/
inductive ProofSpine : {Γ Δ : List (NormalForm P)} → G P Γ Δ →
    {Θ Λ : List (NormalForm P)} → G P Θ Λ → Type u where
  | root {Γ Δ} (g : G P Γ Δ) : ProofSpine g g
  | down {Γ Δ Θ Λ Ξ Ω} {f : G P Γ Δ} {g : G P Θ Λ} {h : G P Ξ Ω}
      (p : Premise f g) (a : ProofSpine g h) : ProofSpine f h

namespace ProofSpine
variable {Γ Δ Θ Λ Ξ Ω : List (NormalForm P)}
variable {f : G P Γ Δ} {g : G P Θ Λ} {h : G P Ξ Ω}

def path : {Γ Δ Θ Λ : List (NormalForm P)} → {f : G P Γ Δ} → {g : G P Θ Λ} →
    ProofSpine f g → List Nat
  | _,_,_,_,_,_,.root _ => []
  | _,_,_,_,_,_,.down p a => p.branch :: a.path

def snoc : {Γ Δ Θ Λ Ξ Ω : List (NormalForm P)} → {f : G P Γ Δ} →
    {g : G P Θ Λ} → {h : G P Ξ Ω} → ProofSpine f g → Premise g h → ProofSpine f h
  | _,_,_,_,_,_,_,_,_,.root _,p => .down p (.root _)
  | _,_,_,_,_,_,_,_,_,.down p a,q => .down p (a.snoc q)

def toAddress : {Γ Δ Θ Λ : List (NormalForm P)} → {f : G P Γ Δ} → {g : G P Θ Λ} →
    ProofSpine f g → ProofAddress f g
  | _,_,_,_,_,_,.root _ => .root
  | _,_,_,_,_,_,.down p a => (ProofAddress.root.down p).append a.toAddress

theorem snoc_path (a : ProofSpine f g) (p : Premise g h) :
    (a.snoc p).path = a.path ++ [p.branch] := by
  induction a with
  | root => rfl
  | down q a ih => exact congrArg (List.cons q.branch) (ih p)

theorem toAddress_snoc (a : ProofSpine f g) (p : Premise g h) :
    (a.snoc p).toAddress = a.toAddress.down p := by
  induction a with
  | root => rfl
  | down q a ih =>
    change (ProofAddress.root.down q).append (a.snoc p).toAddress =
      ((ProofAddress.root.down q).append a.toAddress).down p
    rw [ih]
    rfl

theorem toAddress_path (a : ProofSpine f g) : a.toAddress.path = a.path := by
  induction a with
  | root => rfl
  | down p a ih =>
    rw [toAddress,ProofAddress.append_path,ih]
    rfl

theorem eq_of_path (a b : ProofSpine f g) (he : a.path = b.path) : a = b := by
  induction a with
  | root => cases b <;> first | rfl | cases he
  | @down Γ Δ Θ Λ Ξ Ω f j k p a ih =>
    cases b with
    | root => cases he
    | @down _ _ Θ' Λ' _ _ _ j' _ q b =>
      have hp : p.branch = q.branch := (List.cons.inj he).1
      have hb : (⟨_,_,j,p⟩ : Branch f) = ⟨_,_,j',q⟩ := Branch.eq_of_branch _ _ hp
      cases hb
      have ht := ih b (List.cons.inj he).2
      cases ht
      rfl

end ProofSpine

namespace ProofAddress
variable {Γ Δ Θ Λ : List (NormalForm P)} {f : G P Γ Δ} {g : G P Θ Λ}

def spine : {Θ Λ : List (NormalForm P)} → {g : G P Θ Λ} →
    ProofAddress f g → ProofSpine f g
  | _,_,_,.root => .root _
  | _,_,_,.down a p => a.spine.snoc p

theorem spine_toAddress (a : ProofAddress f g) : a.spine.toAddress = a := by
  induction a with
  | root => rfl
  | down a p ih => rw [spine,ProofSpine.toAddress_snoc,ih]

theorem spine_path (a : ProofAddress f g) : a.spine.path = a.path := by
  induction a with
  | root => rfl
  | down a p ih => rw [spine,ProofSpine.snoc_path,ih]; rfl

theorem eq_of_path (a b : ProofAddress f g) (he : a.path = b.path) : a = b := by
  have ht := ProofSpine.eq_of_path a.spine b.spine ((a.spine_path.trans he).trans b.spine_path.symm)
  have hh := congrArg ProofSpine.toAddress ht
  simpa only [spine_toAddress] using hh

end ProofAddress
end DosenPetric.Reduced.Gentzen
