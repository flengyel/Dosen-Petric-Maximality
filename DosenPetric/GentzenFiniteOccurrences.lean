module

public import DosenPetric.GentzenAddressComparison

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

/-- One proof occurrence with its local sequent and dependent address. -/
structure ProofOccurrence {Γ Δ : List (NormalForm P)} (root : G P Γ Δ) where
  source : List (NormalForm P)
  target : List (NormalForm P)
  proof : G P source target
  address : ProofAddress root proof

namespace ProofOccurrence
variable {Γ Δ U V : List (NormalForm P)} {root : G P Γ Δ} {w : G P U V}

def lift (p : Premise root w) (a : ProofOccurrence w) : ProofOccurrence root :=
  ⟨a.source,a.target,a.proof,(ProofAddress.root.down p).append a.address⟩

def atRoot (root : G P Γ Δ) : ProofOccurrence root := ⟨Γ,Δ,root,.root⟩

def ofAddress (a : ProofAddress root w) : ProofOccurrence root := ⟨U,V,w,a⟩

end ProofOccurrence

namespace FiniteEnumeration
def unique {α : Type u} [DecidableEq α] : List α → List α
  | [] => []
  | a::xs => if a ∈ unique xs then unique xs else a::unique xs

theorem mem_unique {α : Type u} [DecidableEq α] (a : α) (xs : List α) :
    a ∈ unique xs ↔ a ∈ xs := by
  induction xs generalizing a with
  | nil => rfl
  | cons b xs ih =>
    simp only [unique]
    split <;> simp_all

theorem unique_nodup {α : Type u} [DecidableEq α] (xs : List α) :
    (unique xs).Nodup := by
  induction xs with
  | nil => exact .nil
  | cons a xs ih =>
    simp only [unique]
    split
    · exact ih
    · exact List.nodup_cons.mpr ⟨by assumption,ih⟩
end FiniteEnumeration

namespace G

/-- Every actual branch occurrence is retained, including identical siblings. -/
def occurrences : {Γ Δ : List (NormalForm P)} → (g : G P Γ Δ) → List (ProofOccurrence g)
  | _,_,.identity l => [ProofOccurrence.atRoot (G.identity l)]
  | _,_,.zero l => [ProofOccurrence.atRoot (G.zero l)]
  | _,_,.topI => [ProofOccurrence.atRoot (G.topI)]
  | _,_,.botE => [ProofOccurrence.atRoot (G.botE)]
  | _,_,.exchangeL Γ X Y Θ Δ f =>
    ProofOccurrence.atRoot (G.exchangeL Γ X Y Θ Δ f) :: (occurrences f).map (ProofOccurrence.lift (Premise.exchangeL Γ X Y Θ Δ f))
  | _,_,.exchangeR Γ Δ X Y Λ f =>
    ProofOccurrence.atRoot (G.exchangeR Γ Δ X Y Λ f) :: (occurrences f).map (ProofOccurrence.lift (Premise.exchangeR Γ Δ X Y Λ f))
  | _,_,.thinL Γ Θ Δ A f =>
    ProofOccurrence.atRoot (G.thinL Γ Θ Δ A f) :: (occurrences f).map (ProofOccurrence.lift (Premise.thinL Γ Θ Δ A f))
  | _,_,.thinR Γ Δ Λ A f =>
    ProofOccurrence.atRoot (G.thinR Γ Δ Λ A f) :: (occurrences f).map (ProofOccurrence.lift (Premise.thinR Γ Δ Λ A f))
  | _,_,.contractL C gs Θ Δ hn f =>
    ProofOccurrence.atRoot (G.contractL C gs Θ Δ hn f) :: (occurrences f).map (ProofOccurrence.lift (Premise.contractL C gs Θ Δ hn f))
  | _,_,.contractR Γ C gs Λ hn f =>
    ProofOccurrence.atRoot (G.contractR Γ C gs Λ hn f) :: (occurrences f).map (ProofOccurrence.lift (Premise.contractR Γ C gs Λ hn f))
  | _,_,.conjL Γ Θ Δ A B f =>
    ProofOccurrence.atRoot (G.conjL Γ Θ Δ A B f) :: (occurrences f).map (ProofOccurrence.lift (Premise.conjL Γ Θ Δ A B f))
  | _,_,.disjR Γ Δ Λ A B f =>
    ProofOccurrence.atRoot (G.disjR Γ Δ Λ A B f) :: (occurrences f).map (ProofOccurrence.lift (Premise.disjR Γ Δ Λ A B f))
  | _,_,.conjR f g =>
    ProofOccurrence.atRoot (G.conjR f g) ::
      ((occurrences f).map (ProofOccurrence.lift (Premise.conjR_left f g)) ++
       (occurrences g).map (ProofOccurrence.lift (Premise.conjR_right f g)))
  | _,_,.disjL f g =>
    ProofOccurrence.atRoot (G.disjL f g) ::
      ((occurrences f).map (ProofOccurrence.lift (Premise.disjL_left f g)) ++
       (occurrences g).map (ProofOccurrence.lift (Premise.disjL_right f g)))
  | _,_,.mix f g =>
    ProofOccurrence.atRoot (G.mix f g) ::
      ((occurrences f).map (ProofOccurrence.lift (Premise.mix_left f g)) ++
       (occurrences g).map (ProofOccurrence.lift (Premise.mix_right f g)))
  | _,_,.cut f g =>
    ProofOccurrence.atRoot (G.cut f g) ::
      ((occurrences f).map (ProofOccurrence.lift (Premise.cut_left f g)) ++
       (occurrences g).map (ProofOccurrence.lift (Premise.cut_right f g)))

theorem occurrences_eq {Γ Δ : List (NormalForm P)} (g : G P Γ Δ) :
    g.occurrences = ProofOccurrence.atRoot g :: g.branches.flatMap
      (fun b => b.proof.occurrences.map (ProofOccurrence.lift b.occurrence)) := by
  cases g <;> simp only [occurrences,branches,List.flatMap_cons,List.flatMap_nil,List.append_nil]

/-- The complete finite occurrence enumeration without duplicate records.+Only equality of whole dependent occurrences is removed. -/
noncomputable def finiteOccurrences {Γ Δ : List (NormalForm P)} (g : G P Γ Δ) :
    List (ProofOccurrence g) := by
  classical
  exact FiniteEnumeration.unique g.occurrences

theorem finiteOccurrences_mem {Γ Δ : List (NormalForm P)} (g : G P Γ Δ)
    (a : ProofOccurrence g) : a ∈ g.finiteOccurrences ↔ a ∈ g.occurrences := by
  classical
  exact FiniteEnumeration.mem_unique a g.occurrences

theorem finiteOccurrences_nodup {Γ Δ : List (NormalForm P)} (g : G P Γ Δ) :
    g.finiteOccurrences.Nodup := by
  classical
  exact FiniteEnumeration.unique_nodup g.occurrences

end G

namespace ProofSpine
variable {Γ Δ U V : List (NormalForm P)} {root : G P Γ Δ} {w : G P U V}

theorem occurrence_mem (a : ProofSpine root w) :
    ProofOccurrence.ofAddress a.toAddress ∈ root.occurrences := by
  induction a with
  | root => rw [G.occurrences_eq]; exact .head _
  | @down Γ Δ U V I J root f w p a ih =>
    rw [G.occurrences_eq]
    apply List.mem_cons_of_mem
    apply List.mem_flatMap.mpr
    refine ⟨⟨U,V,f,p⟩,G.branches_complete _,?_⟩
    exact List.mem_map.mpr ⟨_,ih,rfl⟩

/-- A branch path uniquely determines the dependent proof occurrence. -/
theorem occurrence_eq_of_path {I J : List (NormalForm P)} {v : G P I J}
    (a : ProofSpine root w) (b : ProofSpine root v) (he : a.path = b.path) :
    ProofOccurrence.ofAddress a.toAddress = ProofOccurrence.ofAddress b.toAddress := by
  induction a with
  | root => cases b with
    | root => rfl
    | down p b => cases he
  | @down Γ Δ U V I J root f w p a ih =>
    cases b with
    | root => cases he
    | @down _ _ U' V' I' J' _ f' v q b =>
      have hp : p.branch = q.branch := (List.cons.inj he).1
      have hf : (⟨U,V,f,p⟩ : Branch root) = ⟨U',V',f',q⟩ := Branch.eq_of_branch _ _ hp
      cases hf
      exact congrArg (ProofOccurrence.lift p) (ih b (List.cons.inj he).2)

end ProofSpine

namespace ProofAddress
variable {Γ Δ U V : List (NormalForm P)} {root : G P Γ Δ} {w : G P U V}

theorem occurrence_mem (a : ProofAddress root w) :
    ProofOccurrence.ofAddress a ∈ root.occurrences := by
  simpa only [spine_toAddress] using a.spine.occurrence_mem

theorem occurrence_eq_of_path {I J : List (NormalForm P)} {v : G P I J}
    (a : ProofAddress root w) (b : ProofAddress root v) (he : a.path = b.path) :
    ProofOccurrence.ofAddress a = ProofOccurrence.ofAddress b := by
  have hh := a.spine.occurrence_eq_of_path b.spine
    (by simpa only [spine_path] using he)
  simpa only [spine_toAddress] using hh

end ProofAddress

end DosenPetric.Reduced.Gentzen
