module

public import DosenPetric.GentzenNormalRetracts

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

/-- Distribute a product of two DNF objects using the explicit split comparisons. -/
theorem dnf_product {A B : NormalForm P} (d : DNF A) (e : DNF B) :
    ∃ (C : NormalForm P) (_ : NormalRetract (.conj A B) C), DNF C := by
  induction d generalizing B with
  | pure hA =>
    induction e with
    | pure hB => exact ⟨_,NormalRetract.refl _,DNF.pure ⟨hA,hB⟩⟩
    | @disj B D e f ih ih' =>
      obtain ⟨X,r,hX⟩ := ih
      obtain ⟨Y,s,hY⟩ := ih'
      exact ⟨_,(NormalRetract.dnfRight _ B D).trans (r.tensor .disj s),DNF.disj hX hY⟩
  | @disj A D d f ih ih' =>
    obtain ⟨X,r,hX⟩ := ih e
    obtain ⟨Y,s,hY⟩ := ih' e
    exact ⟨_,(NormalRetract.dnfLeft A D B).trans (r.tensor .disj s),DNF.disj hX hY⟩

/-- The separately typed coproduct expansion yields CNF with a proved recovery. -/
theorem cnf_sum {A B : NormalForm P} (d : CNF A) (e : CNF B) :
    ∃ (C : NormalForm P) (_ : NormalRetract (.disj A B) C), CNF C := by
  induction d generalizing B with
  | pure hA =>
    induction e with
    | pure hB => exact ⟨_,NormalRetract.refl _,CNF.pure ⟨hA,hB⟩⟩
    | @conj B D e f ih ih' =>
      obtain ⟨X,r,hX⟩ := ih
      obtain ⟨Y,s,hY⟩ := ih'
      exact ⟨_,(NormalRetract.cnfRight _ B D).trans (r.tensor .conj s),CNF.conj hX hY⟩
  | @conj A D d f ih ih' =>
    obtain ⟨X,r,hX⟩ := ih e
    obtain ⟨Y,s,hY⟩ := ih' e
    exact ⟨_,(NormalRetract.cnfLeft A D B).trans (r.tensor .conj s),CNF.conj hX hY⟩

/-- Every object is a retract of an explicit disjunctive normal-form expansion. -/
theorem dnf_expansion (A : NormalForm P) :
    ∃ (B : NormalForm P) (_ : NormalRetract A B), DNF B := by
  induction A with
  | lit l => exact ⟨_,NormalRetract.refl _,DNF.pure True.intro⟩
  | top => exact ⟨_,NormalRetract.refl _,DNF.pure True.intro⟩
  | bot => exact ⟨_,NormalRetract.refl _,DNF.pure True.intro⟩
  | conj A B ih ih' =>
    obtain ⟨C,r,hC⟩ := ih
    obtain ⟨D,s,hD⟩ := ih'
    obtain ⟨E,t,hE⟩ := dnf_product hC hD
    exact ⟨E,(r.tensor .conj s).trans t,hE⟩
  | disj A B ih ih' =>
    obtain ⟨C,r,hC⟩ := ih
    obtain ⟨D,s,hD⟩ := ih'
    exact ⟨_,r.tensor .disj s,DNF.disj hC hD⟩

/-- CNF has its own explicit represented maps and one-sided recovery equation. -/
theorem cnf_expansion (A : NormalForm P) :
    ∃ (B : NormalForm P) (_ : NormalRetract A B), CNF B := by
  induction A with
  | lit l => exact ⟨_,NormalRetract.refl _,CNF.pure True.intro⟩
  | top => exact ⟨_,NormalRetract.refl _,CNF.pure True.intro⟩
  | bot => exact ⟨_,NormalRetract.refl _,CNF.pure True.intro⟩
  | conj A B ih ih' =>
    obtain ⟨C,r,hC⟩ := ih
    obtain ⟨D,s,hD⟩ := ih'
    exact ⟨_,r.tensor .conj s,CNF.conj hC hD⟩
  | disj A B ih ih' =>
    obtain ⟨C,r,hC⟩ := ih
    obtain ⟨D,s,hD⟩ := ih'
    obtain ⟨E,t,hE⟩ := cnf_sum hC hD
    exact ⟨E,(r.tensor .disj s).trans t,hE⟩

end DosenPetric.Reduced.Gentzen
