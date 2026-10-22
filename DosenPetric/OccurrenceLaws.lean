module

public import DosenPetric.Structure

@[expose] public section

set_option autoImplicit false

namespace DosenPetric.OccurrenceInterpretation

universe u v

variable {P : Type u} {C : Category.{u,v} (Formula P)} {S : Structure C}
  {Z : ZeroIdentity C} (I : OccurrenceInterpretation S Z)

theorem map_zeroOf {A B : Formula P} (f : C.Hom A B) :
    I.map (Z.zeroOf f) = Relations.empty := by
  rw [ZeroIdentity.zeroOf, I.map_comp, I.map_zero, Relations.empty_comp]

theorem map_prodMap {A B D E : Formula P} (f : C.Hom A D) (g : C.Hom B E) :
    I.map (S.prodMap f g) = Relations.sumMap (I.map f) (I.map g) := by
  rw [Structure.prodMap, I.map_pair, I.map_comp, I.map_comp, I.map_fst, I.map_snd]
  exact Relations.pair_map (I.map f) (I.map g)

theorem map_swap (A : Formula P) : I.map (S.swap A) = Relations.graph Relations.swap := by
  rw [Structure.swap, I.map_pair, I.map_snd, I.map_fst]
  funext x y
  apply propext
  cases x <;> cases y <;> simp [Relations.pair, Relations.fstRel, Relations.sndRel,
    Relations.graph, Relations.swap]

theorem map_u (A B : Formula P) : I.map (S.u A B) = Relations.uRel A.Occ B.Occ := by
  rw [Structure.u, I.map_comp, I.map_prodMap, I.map_id, I.map_inr, I.map_dist]
  rfl

theorem map_fold (A B : Formula P) : I.map (S.fold A B) = Relations.hRel A.Occ B.Occ := by
  rw [Structure.fold, I.map_comp, I.map_u, I.map_copair, I.map_fst, I.map_id]
  rfl

include I

theorem fold_independent (A B D : Formula P) : S.fold A B = S.fold A D := by
  apply I.faithful
  rw [I.map_fold, I.map_fold]
  exact Relations.hRel_independent A.Occ B.Occ D.Occ

theorem fold_swap (A B : Formula P) : C.comp (S.swap A) (S.fold A B) = S.fold A B := by
  apply I.faithful
  rw [I.map_comp, I.map_swap, I.map_fold]
  exact Relations.hRel_swap A.Occ B.Occ

theorem first_injection (A B D : Formula P) :
    C.comp (S.prodMap (C.id A) (S.inl B D)) (S.dist A B D) = S.inl (.conj A B) D := by
  apply I.faithful
  rw [I.map_comp, I.map_prodMap, I.map_id, I.map_inl, I.map_dist, I.map_inl]
  exact Relations.first_injection A.Occ B.Occ D.Occ

theorem second_block (A : Formula P) :
    C.comp (S.u A .bot)
      (S.copair (Z.zeroOf (C.comp (S.fst A .bot) (S.j A))) (S.j A)) =
      C.comp (S.snd A A) (S.j A) := by
  apply I.faithful
  rw [I.map_comp, I.map_u, I.map_copair, I.map_zeroOf, Structure.j, I.map_inl,
    I.map_comp, I.map_snd, I.map_inl]
  exact Relations.second_block A.Occ Empty

/-- A composite through the terminal formula has no intermediate occurrences. -/
theorem through_top {A B : Formula P} (f : C.Hom A .top) (g : C.Hom .top B)
    (w : C.Hom A B) : C.comp f g = Z.zeroOf w := by
  apply I.faithful
  rw [I.map_comp, I.map_zeroOf]
  funext x y
  apply propext
  constructor
  · rintro ⟨e, _, _⟩
    exact Empty.elim e
  · exact False.elim

end DosenPetric.OccurrenceInterpretation
