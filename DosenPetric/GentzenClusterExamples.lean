module

public import DosenPetric.GentzenTraceCompatibility

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

namespace G

theorem identity_leaf (l : Literal P) (s : SequentSide)
    {C : NormalForm P} (x : Place s [.lit l] [.lit l] C) : (identity l).Leaf s x := by cases s <;> rfl

theorem zero_leaf (l : Literal P) (s : SequentSide)
    {C : NormalForm P} (x : Place s [.lit l] [.lit l] C) : (zero l).Leaf s x := by cases s <;> rfl

theorem topI_rank : (topI : G P [] [.top]).rho .right (.here .top []) = 1 := rho_leaf _ _ _ rfl
theorem botE_rank : (botE : G P [.bot] []).rho .left (.here .bot []) = 1 := rho_leaf _ _ _ rfl

theorem zero_rank (l : Literal P) (s : SequentSide)
    {C : NormalForm P} (x : Place s [.lit l] [.lit l] C) : (zero l).rho s x = 1 :=
  rho_leaf _ _ _ (zero_leaf l s x)

theorem signed_identity_ranks (p : P) :
    (identity (.pos p)).rho .left (.here (.lit (.pos p)) []) = 1 ∧
    (identity (.neg p)).rho .right (.here (.lit (.neg p)) []) = 1 :=
  ⟨rho_leaf _ _ _ (identity_leaf _ _ _),rho_leaf _ _ _ (identity_leaf _ _ _)⟩

theorem conjL_principal_leaf (Γ Θ Δ : List (NormalForm P)) (A B : NormalForm P)
    (f : G P (Γ ++ A :: B :: Θ) Δ) :
    (conjL Γ Θ Δ A B f).Leaf .left (At.shift Γ (.here (.conj A B) Θ)) := by
  change (if (At.shift Γ (.here (.conj A B) Θ)).index = Γ.length then 0 else 1) = 0
  have h : (At.shift Γ (.here (.conj A B) Θ)).index = Γ.length := by simp [At.index_shift,At.index]
  rw [ite_eq_left h]

theorem disjR_principal_leaf (Γ Δ Λ : List (NormalForm P)) (A B : NormalForm P)
    (f : G P Γ (Δ ++ A :: B :: Λ)) :
    (disjR Γ Δ Λ A B f).Leaf .right (At.shift Δ (.here (.disj A B) Λ)) := by
  change (if (At.shift Δ (.here (.disj A B) Λ)).index = Δ.length then 0 else 1) = 0
  have h : (At.shift Δ (.here (.disj A B) Λ)).index = Δ.length := by simp [At.index_shift,At.index]
  rw [ite_eq_left h]

theorem conjR_principal_leaf {Γ Θ Δ Λ : List (NormalForm P)} {A B : NormalForm P}
    (f : G P Γ (A :: Δ)) (g : G P Θ (B :: Λ)) :
    (conjR f g).Leaf .right (.here (.conj A B) (Δ ++ Λ)) := rfl

theorem disjL_principal_leaf {Γ Θ Δ Λ : List (NormalForm P)} {A B : NormalForm P}
    (f : G P (A :: Γ) Δ) (g : G P (B :: Θ) Λ) :
    (disjL f g).Leaf .left (.here (.disj A B) (Γ ++ Θ)) := rfl

theorem repeated_positions_distinct (C : NormalForm P) (Γ Δ : List (NormalForm P))
    (f : G P (C :: C :: Γ) Δ) :
    f.traceRoot .left (.here C (C :: Γ)) ≠ f.traceRoot .left (.there (.here C Γ)) := by
  intro h
  have hi := congrArg (fun n : TraceNode P .left C => n.position.index) h
  change 0 = 1 at hi
  cases hi

theorem duplicate_subproof_addresses {Γ Δ : List (NormalForm P)} (f : G P Γ Δ) :
    ((ProofAddress.root : ProofAddress (mix f f) (mix f f)).down (Premise.mix_left f f)).path ≠
    ((ProofAddress.root : ProofAddress (mix f f) (mix f f)).down (Premise.mix_right f f)).path := by
  simp [ProofAddress.path,Premise.branch]

theorem three_copy_offsets (C : NormalForm P) :
    (selectedCopies C [[],[C],[]] []).map At.index = [0,2,3] :=
  (selectedCopies_indices C [[],[C],[]] []).trans rfl

theorem three_copies_with_fixed_equal (C : NormalForm P) (Δ : List (NormalForm P))
    (f : G P (repeated C [[],[C],[]] ++ []) Δ) :
    (contractL C [[],[C],[]] [] Δ (by change 2 ≤ 3; exact Nat.le_succ 2) f).sourceArity .left
      (At.shift (gaps [[],[C],[]]) (.here C [])) = 3 := rfl

theorem topmost_cluster_properties {Γ Θ Δ Λ : List (NormalForm P)} {C : NormalForm P}
    (f : G P Γ (C :: Δ)) (g : G P (C :: Θ) Λ) (ht : Topmost f g)
    (hf : f.Atomized) (hg : g.Atomized) :
    (∀ n ∈ (f.cluster .right (.here C Δ)).nodes, n.proof.CutFree ∧ n.proof.Atomized) ∧
    (∀ n ∈ (g.cluster .left (.here C Θ)).nodes, n.proof.CutFree ∧ n.proof.Atomized) := by
  constructor
  · intro n hn; exact ⟨f.cluster_cutFree _ _ ht.1 n hn,f.cluster_atomized _ _ hf n hn⟩
  · intro n hn; exact ⟨g.cluster_cutFree _ _ ht.2 n hn,g.cluster_atomized _ _ hg n hn⟩

end G

theorem swap_empty_blocks (Θ : List (NormalForm P)) {C : NormalForm P} (a : At Θ C) :
    a.swapBlocks [] [] [] Θ = a := by
  apply At.index_injective
  have h := swapBlocks_index [] [] [] Θ a
  simpa only [List.length_nil,exchangeIndex,Nat.not_lt_zero,ite_false,Nat.zero_add] using h

namespace Premise

theorem cut_left_consumed {Γ Θ Δ Λ : List (NormalForm P)} {C : NormalForm P}
    (f : G P Γ (C :: Δ)) (g : G P (C :: Θ) Λ) :
    (cut_left f g).parent .right (.here C Δ) = none := rfl

theorem cut_right_consumed {Γ Θ Δ Λ : List (NormalForm P)} {C : NormalForm P}
    (f : G P Γ (C :: Δ)) (g : G P (C :: Θ) Λ) :
    (cut_right f g).parent .left (.here C Θ) = none := rfl

theorem cut_left_source {Γ Θ Δ Λ : List (NormalForm P)} {C A : NormalForm P}
    (f : G P Γ (C :: Δ)) (g : G P (C :: Θ) Λ) (a : At Γ A) :
    (cut_left f g).parent .left a = some (At.shift Θ a) := rfl

theorem cut_left_target {Γ Θ Δ Λ : List (NormalForm P)} {C A : NormalForm P}
    (f : G P Γ (C :: Δ)) (g : G P (C :: Θ) Λ) (a : At Δ A) :
    (cut_left f g).parent .right a.there = some (At.shift Λ a) := rfl

theorem cut_right_source {Γ Θ Δ Λ : List (NormalForm P)} {C A : NormalForm P}
    (f : G P Γ (C :: Δ)) (g : G P (C :: Θ) Λ) (a : At Θ A) :
    (cut_right f g).parent .left a.there = some (a.before Γ) := rfl

theorem cut_right_target {Γ Θ Δ Λ : List (NormalForm P)} {C A : NormalForm P}
    (f : G P Γ (C :: Δ)) (g : G P (C :: Θ) Λ) (a : At Λ A) :
    (cut_right f g).parent .right a = some (a.before Δ) := rfl

end Premise
end DosenPetric.Reduced.Gentzen
