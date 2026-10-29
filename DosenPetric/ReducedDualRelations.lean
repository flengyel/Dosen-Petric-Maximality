module

public import DosenPetric.ReducedDualCoordinates

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Term
universe u
variable {P : Type u}
open NormalForm

theorem relation_distRight (A B C : NormalForm P) :
    (distRight A B C).relation = Relations.graph Presentation.Occurrence.unassoc := by
  rw [relation_toFull]
  exact Presentation.Term.relation_distRight A.formula B.formula C.formula

/-- The term reflection reverses the complete tagged relation, under the
explicit sign-flipping occurrence bijections. -/
theorem dual_relation {A B : NormalForm P} (f : Term P A B)
    (x : A.formula.Occ) (y : B.formula.Occ) :
    f.dual.relation (toDual B y) (toDual A x) ↔ f.relation x y := by
  induction f with
  | id A =>
    change toDual A y = toDual A x ↔ x = y
    rw [toDual_eq_iff]
    exact eq_comm
  | @comp A B C f g ih ih' =>
    change (∃ q, g.dual.relation (toDual C y) q ∧ f.dual.relation q (toDual A x)) ↔
      ∃ b, f.relation x b ∧ g.relation b y
    constructor
    · rintro ⟨q,hg,hf⟩
      refine ⟨fromDual B q,(ih x (fromDual B q)).mp ?_,(ih' (fromDual B q) y).mp ?_⟩
      · rw [to_fromDual]; exact hf
      · rw [to_fromDual]; exact hg
    · rintro ⟨b,hf,hg⟩
      exact ⟨toDual B b,(ih' b y).mpr hg,(ih x b).mpr hf⟩
  | tensor o f g ih ih' =>
    cases o <;> cases x <;> cases y <;>
      simp [dual,relation,toDual,Relations.sumMap,ih,ih']
  | assocR o A B C =>
    cases o <;> rcases x with x | (x | x) <;> rcases y with (y | y) | y <;>
      simp [dual,relation,toDual,Relations.graph,Relations.reassoc,
        Presentation.Occurrence.unassoc,toDual_eq_iff,eq_comm]
  | assocL o A B C =>
    cases o <;> rcases x with (x | x) | x <;> rcases y with y | (y | y) <;>
      simp [dual,relation,toDual,Relations.graph,Relations.reassoc,
        Presentation.Occurrence.unassoc,toDual_eq_iff,eq_comm]
  | swap o A B =>
    cases o <;> cases x <;> cases y <;>
      simp [dual,relation,toDual,Relations.graph,Presentation.Occurrence.exchange,toDual_eq_iff,eq_comm]
  | diag A =>
    cases y <;> simp [dual,relation,toDual,Relations.pair,Relations.copair,Relations.graph,toDual_eq_iff,eq_comm]
  | codiag A =>
    cases x <;> simp [dual,relation,toDual,Relations.pair,Relations.copair,Relations.graph,toDual_eq_iff,eq_comm]
  | fst A B =>
    cases x <;> simp [dual,relation,toDual,Relations.fstRel,Relations.graph,toDual_eq_iff,eq_comm]
  | snd A B =>
    cases x <;> simp [dual,relation,toDual,Relations.sndRel,Relations.graph,toDual_eq_iff,eq_comm]
  | inl A B =>
    cases y <;> simp [dual,relation,toDual,Relations.fstRel,Relations.graph,toDual_eq_iff,eq_comm]
  | inr A B =>
    cases y <;> simp [dual,relation,toDual,Relations.sndRel,Relations.graph,toDual_eq_iff,eq_comm]
  | rightOut o A =>
    cases o <;> rcases x with x | e <;>
      first | cases e | simp [dual,relation,toDual,Relations.graph,Presentation.Occurrence.dropRight,toDual_eq_iff,eq_comm]
  | rightIn o A =>
    cases o <;> rcases y with y | e <;>
      first | cases e | simp [dual,relation,toDual,Relations.graph,Presentation.Occurrence.dropRight,toDual_eq_iff,eq_comm]
  | leftOut o A =>
    cases o <;> rcases x with e | x <;>
      first | cases e | simp [dual,relation,toDual,Relations.graph,Presentation.Occurrence.dropLeft,toDual_eq_iff,eq_comm]
  | leftIn o A =>
    cases o <;> rcases y with e | y <;>
      first | cases e | simp [dual,relation,toDual,Relations.graph,Presentation.Occurrence.dropLeft,toDual_eq_iff,eq_comm]
  | mix A B =>
    cases x <;> cases y <;> simp [dual,relation,toDual,Relations.graph,toDual_eq_iff,eq_comm]
  | dist A B C =>
    simp only [dual,relation_distRight]
    rcases x with x | (x | x) <;> rcases y with (y | y) | y <;>
      simp [relation,toDual,Relations.graph,Relations.reassoc,Presentation.Occurrence.unassoc,toDual_eq_iff,eq_comm]
    all_goals constructor
    all_goals intro h
    all_goals first
      | exact (toDual_eq_iff _ _ _).mp (Sum.inl.inj h)
      | exact (toDual_eq_iff _ _ _).mp (Sum.inr.inj h)
      | cases h; rfl
  | zero A => rfl
  | eta p => cases x
  | epsilon p => cases y

end DosenPetric.Reduced.Term
