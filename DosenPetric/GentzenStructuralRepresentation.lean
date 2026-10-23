module

public import DosenPetric.GentzenCartesian

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.Represented
universe u
variable {P : Type u}

theorem toTop (A : NormalForm P) : Represented (Reduced.toTop A) := by
  let g : G P [A] [.top] := .thinL [] [] [.top] A .topI
  exact ⟨g, ((conjDiagonal P).toUnit_unique _).trans ((conjDiagonal P).toUnit_unique _).symm⟩

theorem fromBot (A : NormalForm P) : Represented (Reduced.fromBot A) := by
  let g : G P [.bot] [A] := .thinR [.bot] [] [] A .botE
  exact ⟨g, ((disjDiagonal P).toUnit_unique _).trans ((disjDiagonal P).toUnit_unique _).symm⟩

theorem assocR (o : Op) (A B C : NormalForm P) : Represented (Reduced.assocR o A B C) := by
  cases o with
  | conj =>
    have h := (conjDiagonal P).assocR_pair (rightOut_assocR .conj) A B C
    change Reduced.assocR .conj A B C =
      Reduced.pair (Reduced.pair (Reduced.fst A (.conj B C))
        (Reduced.comp (Reduced.snd A (.conj B C)) (Reduced.fst B C)))
        (Reduced.comp (Reduced.snd A (.conj B C)) (Reduced.snd B C)) at h
    rw [h]
    exact ((fst ..).pair ((snd ..).comp (fst ..))).pair ((snd ..).comp (snd ..))
  | disj =>
    have h := (disjDiagonal P).assocL_pair (rightIn_assocL .disj) A B C
    change Reduced.assocR .disj A B C =
      Reduced.copair (Reduced.comp (Reduced.inl A B) (Reduced.inl (.disj A B) C))
        (Reduced.copair (Reduced.comp (Reduced.inr A B) (Reduced.inl (.disj A B) C))
          (Reduced.inr (.disj A B) C)) at h
    rw [h]
    exact ((inl ..).comp (inl ..)).copair (((inr ..).comp (inl ..)).copair (inr ..))

theorem assocL (o : Op) (A B C : NormalForm P) : Represented (Reduced.assocL o A B C) := by
  cases o with
  | conj =>
    have h := (conjDiagonal P).assocL_pair (rightOut_assocR .conj) A B C
    change Reduced.assocL .conj A B C =
      Reduced.pair (Reduced.comp (Reduced.fst (.conj A B) C) (Reduced.fst A B))
        (Reduced.pair (Reduced.comp (Reduced.fst (.conj A B) C) (Reduced.snd A B))
          (Reduced.snd (.conj A B) C)) at h
    rw [h]
    exact ((fst ..).comp (fst ..)).pair (((fst ..).comp (snd ..)).pair (snd ..))
  | disj =>
    have h := (disjDiagonal P).assocR_pair (rightIn_assocL .disj) A B C
    change Reduced.assocL .disj A B C =
      Reduced.copair (Reduced.copair (Reduced.inl A (.disj B C))
        (Reduced.comp (Reduced.inl B C) (Reduced.inr A (.disj B C))))
        (Reduced.comp (Reduced.inr B C) (Reduced.inr A (.disj B C))) at h
    rw [h]
    exact ((inl ..).copair ((inl ..).comp (inr ..))).copair ((inr ..).comp (inr ..))

theorem swap (o : Op) (A B : NormalForm P) : Represented (Reduced.swap o A B) := by
  cases o with
  | conj =>
    have h : Reduced.swap .conj A B = Reduced.pair (Reduced.snd A B) (Reduced.fst A B) := by
      apply conj_ext
      · rw [← Laws.snd_swap]
        exact ((conjDiagonal P).pair_fst (Reduced.snd A B) (Reduced.fst A B)).symm
      · rw [swap_snd]
        exact ((conjDiagonal P).pair_snd (Reduced.snd A B) (Reduced.fst A B)).symm
    rw [h]
    exact (snd ..).pair (fst ..)
  | disj =>
    have h : Reduced.swap .disj A B = Reduced.copair (Reduced.inr B A) (Reduced.inl B A) := by
      apply disj_ext
      · rw [← Laws.inr_swap]
        exact ((disjDiagonal P).pair_fst (Reduced.inr B A) (Reduced.inl B A)).symm
      · have hs : Reduced.comp (Reduced.inr A B) (Reduced.swap .disj A B) = Reduced.inl B A := by
          rw [Laws.inr_swap, Laws.assoc, Laws.swap_swap, Laws.comp_id]
        rw [hs]
        exact ((disjDiagonal P).pair_snd (Reduced.inr B A) (Reduced.inl B A)).symm
    rw [h]
    exact (inr ..).copair (inl ..)

theorem rightOut (o : Op) (A : NormalForm P) : Represented (Reduced.rightOut o A) := by
  cases o with
  | conj => rw [← Laws.fst_top]; exact fst ..
  | disj =>
    have h : Reduced.rightOut .disj A = Reduced.copair (Reduced.id A) (Reduced.fromBot A) := by
      apply disj_ext
      · rw [Laws.inl_bot, Laws.rightIn_Out]
        have hp := (disjDiagonal P).pair_fst (Reduced.id A) (Reduced.fromBot A)
        change Reduced.comp (Reduced.inl A .bot) (Reduced.copair (Reduced.id A) (Reduced.fromBot A)) = Reduced.id A at hp
        rw [Laws.inl_bot] at hp
        exact hp.symm
      · exact ((disjDiagonal P).toUnit_unique _).trans ((disjDiagonal P).toUnit_unique _).symm
    rw [h]
    exact (identity A).copair (fromBot A)

theorem leftOut (o : Op) (A : NormalForm P) : Represented (Reduced.leftOut o A) := by
  cases o with
  | conj =>
    have h : Reduced.snd .top A = Reduced.leftOut .conj A := (conjDiagonal P).snd_unit A
    rw [← h]; exact snd ..
  | disj =>
    have h : Reduced.leftOut .disj A = Reduced.copair (Reduced.fromBot A) (Reduced.id A) := by
      apply disj_ext
      · exact ((disjDiagonal P).toUnit_unique _).trans ((disjDiagonal P).toUnit_unique _).symm
      · have hu : Reduced.inr .bot A = Reduced.leftIn .disj A := (disjDiagonal P).snd_unit A
        rw [hu, Laws.leftIn_Out]
        have hp := (disjDiagonal P).pair_snd (Reduced.fromBot A) (Reduced.id A)
        change Reduced.comp (Reduced.inr .bot A) (Reduced.copair (Reduced.fromBot A) (Reduced.id A)) = Reduced.id A at hp
        rw [hu] at hp
        exact hp.symm
    rw [h]
    exact (fromBot A).copair (identity A)

theorem rightIn (o : Op) (A : NormalForm P) : Represented (Reduced.rightIn o A) := by
  cases o with
  | disj => rw [← Laws.inl_bot]; exact inl ..
  | conj =>
    have h : Reduced.rightIn .conj A = Reduced.pair (Reduced.id A) (Reduced.toTop A) := by
      apply conj_ext
      · rw [Laws.fst_top, Laws.rightIn_Out]
        have hp := (conjDiagonal P).pair_fst (Reduced.id A) (Reduced.toTop A)
        change Reduced.comp (Reduced.pair (Reduced.id A) (Reduced.toTop A)) (Reduced.fst A .top) = Reduced.id A at hp
        rw [Laws.fst_top] at hp
        exact hp.symm
      · exact ((conjDiagonal P).toUnit_unique _).trans ((conjDiagonal P).toUnit_unique _).symm
    rw [h]
    exact (identity A).pair (toTop A)

theorem leftIn (o : Op) (A : NormalForm P) : Represented (Reduced.leftIn o A) := by
  cases o with
  | disj =>
    have h : Reduced.inr .bot A = Reduced.leftIn .disj A := (disjDiagonal P).snd_unit A
    rw [← h]; exact inr ..
  | conj =>
    have h : Reduced.leftIn .conj A = Reduced.pair (Reduced.toTop A) (Reduced.id A) := by
      apply conj_ext
      · exact ((conjDiagonal P).toUnit_unique _).trans ((conjDiagonal P).toUnit_unique _).symm
      · have hu : Reduced.snd .top A = Reduced.leftOut .conj A := (conjDiagonal P).snd_unit A
        rw [hu, Laws.leftIn_Out]
        have hp := (conjDiagonal P).pair_snd (Reduced.toTop A) (Reduced.id A)
        change Reduced.comp (Reduced.pair (Reduced.toTop A) (Reduced.id A)) (Reduced.snd .top A) = Reduced.id A at hp
        rw [hu] at hp
        exact hp.symm
    rw [h]
    exact (toTop A).pair (identity A)

end DosenPetric.Reduced.Gentzen.Represented
