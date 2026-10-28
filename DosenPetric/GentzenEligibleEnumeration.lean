module

public import DosenPetric.GentzenEligibleCorrespondence

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u} {Γ Δ : List (NormalForm P)}
namespace EligibleEnumeration
variable (root : G P Γ Δ) (s : SequentSide) (C : NormalForm P)
variable (Q : (o : ProofOccurrence root) → Place s o.source o.target C → Prop)

/-- Each occurrence contributes its path and its eligible lower-contraction rank. -/
noncomputable def key (o : ProofOccurrence root) : Option (List Nat × Nat) := by
  classical
  exact if he : ∃ x, Q o x then
    some (o.address.path,o.proof.rho s he.choose) else none

theorem key_path (o : ProofOccurrence root) (k : List Nat × Nat)
    (hk : key root s C Q o = some k) : k.1 = o.address.path := by
  classical
  unfold key at hk
  split at hk
  · exact (congrArg Prod.fst (Option.some.inj hk)).symm
  · cases hk

theorem key_spec
    (hQ : ∀ (o : ProofOccurrence root) (x : Place s o.source o.target C),
      Q o x → o.proof.LowerContraction s x)
    (o : ProofOccurrence root) (k : List Nat × Nat) :
    key root s C Q o = some k ↔
      ∃ x, Q o x ∧ k = (o.address.path,o.proof.rho s x) := by
  classical
  unfold key
  split
  · rename_i he
    constructor
    · intro hk
      exact ⟨he.choose,he.choose_spec,(Option.some.inj hk).symm⟩
    · rintro ⟨x,hx,rfl⟩
      have hi := o.proof.lowerContraction_index_unique s he.choose x
        (hQ o _ he.choose_spec) (hQ o _ hx)
      have hh : he.choose = x := by cases s <;> exact At.index_injective _ _ hi
      rw [hh]
  · rename_i he
    constructor
    · intro hh; cases hh
    · rintro ⟨x,hx,_⟩; exact False.elim (he ⟨x,hx⟩)

noncomputable def keys : List (List Nat × Nat) :=
  root.finiteOccurrences.filterMap (key root s C Q)

theorem keys_nodup : (keys root s C Q).Nodup := by
  apply List.Pairwise.filterMap _ _ root.finiteOccurrences_nodup
  intro a b hn k hk k' hk' he
  apply hn
  have ha := key_path root s C Q a k hk
  have hb := key_path root s C Q b k' hk'
  have hp : a.address.path = b.address.path := ha.symm.trans ((congrArg Prod.fst he).trans hb)
  exact a.address.occurrence_eq_of_path b.address hp

theorem keys_path_unique {k k' : List Nat × Nat}
    (hk : k ∈ keys root s C Q) (hk' : k' ∈ keys root s C Q) (hp : k.1 = k'.1) : k = k' := by
  obtain ⟨a,_,ha⟩ := List.mem_filterMap.mp hk
  obtain ⟨b,_,hb⟩ := List.mem_filterMap.mp hk'
  have hpa := key_path root s C Q a k ha
  have hpb := key_path root s C Q b k' hb
  have he : a = b := a.address.occurrence_eq_of_path b.address
    (hpa.symm.trans (hp.trans hpb))
  cases he
  exact Option.some.inj (ha.symm.trans hb)

theorem mem_keys
    (hQ : ∀ (o : ProofOccurrence root) (x : Place s o.source o.target C),
      Q o x → o.proof.LowerContraction s x) (k : List Nat × Nat) :
    k ∈ keys root s C Q ↔
      ∃ (o : ProofOccurrence root) (x : Place s o.source o.target C),
        Q o x ∧ k = (o.address.path,o.proof.rho s x) := by
  constructor
  · intro hk
    obtain ⟨o,_,ho⟩ := List.mem_filterMap.mp hk
    obtain ⟨x,hx,hk⟩ := (key_spec root s C Q hQ o k).mp ho
    exact ⟨o,x,hx,hk⟩
  · rintro ⟨o,x,hx,hk⟩
    apply List.mem_filterMap.mpr
    refine ⟨o,?_,(key_spec root s C Q hQ o k).mpr ⟨x,hx,hk⟩⟩
    exact (root.finiteOccurrences_mem o).mpr o.address.occurrence_mem

end EligibleEnumeration

namespace EligibleSites
variable {C : NormalForm P} {Θ Λ : List (NormalForm P)}
variable (f : G P Γ (C::Δ)) (g : G P (C::Θ) Λ)

noncomputable def left : List (List Nat × Nat) :=
  EligibleEnumeration.keys g .left C (fun o x => ReducibleL f g o.address x)

noncomputable def right : List (List Nat × Nat) :=
  EligibleEnumeration.keys f .right C (fun o x => ReducibleR f g o.address x)

theorem mem_left (k : List Nat × Nat) :
    k ∈ left f g ↔ ∃ (o : ProofOccurrence g) (x : At o.source C),
      ReducibleL f g o.address x ∧ k = (o.address.path,o.proof.rho .left x) :=
  EligibleEnumeration.mem_keys g .left C _ (fun _ _ hx => hx.2.1.2) k

theorem mem_right (k : List Nat × Nat) :
    k ∈ right f g ↔ ∃ (o : ProofOccurrence f) (x : At o.target C),
      ReducibleR f g o.address x ∧ k = (o.address.path,o.proof.rho .right x) :=
  EligibleEnumeration.mem_keys f .right C _ (fun _ _ hx => hx.2.1.2) k

theorem left_nodup : (left f g).Nodup := EligibleEnumeration.keys_nodup ..
theorem right_nodup : (right f g).Nodup := EligibleEnumeration.keys_nodup ..

theorem left_path_unique {k k' : List Nat × Nat}
    (hk : k ∈ left f g) (hk' : k' ∈ left f g) (hp : k.1 = k'.1) : k = k' :=
  EligibleEnumeration.keys_path_unique g .left C _ hk hk' hp

theorem right_path_unique {k k' : List Nat × Nat}
    (hk : k ∈ right f g) (hk' : k' ∈ right f g) (hp : k.1 = k'.1) : k = k' :=
  EligibleEnumeration.keys_path_unique f .right C _ hk hk' hp

end EligibleSites
end DosenPetric.Reduced.Gentzen
