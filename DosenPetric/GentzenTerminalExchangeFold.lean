module

public import DosenPetric.GentzenTerminalFoldComponents

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.BlockedLeftDisj
universe u
variable {P : Type u}

theorem terminalExchange_arrow (F : List (NormalForm P)) (A : NormalForm P) (I : List (NormalForm P)) :
    (terminalExchange F A I).arrow .conj =
      comp (ofTerm (append .conj (F++[A]) I).invTerm)
        (comp (tensor .conj (TerminalFold.out F A) (id (ante I)))
          (comp (terminalCross (ante F) A (ante I))
            (comp (tensor .conj (ofTerm (append .conj F I).toTerm) (id A))
              (TerminalFold.into (F++I) A)))) := by
  apply product_positions
  intro B b
  have hs := ExchangeScript.component (terminalExchange F A I) .conj b
  change comp ((terminalExchange F A I).arrow .conj) (ofTerm b.projection) =
    ofTerm ((terminalExchange F A I).get b).projection at hs
  rw [hs]
  cases At.cases_append (F++I) [A] b with
  | inl hb =>
    obtain ⟨b,rfl⟩ := hb
    cases At.cases_append F I b with
    | inl hb =>
      obtain ⟨b,rfl⟩ := hb
      rw [terminalExchange_before]
      simp only [Laws.assoc,TerminalFold.into_before,TerminalFold.join_before,
        TerminalFold.out_before,TerminalFold.split_before,terminalCross,
        ProductCalculation.tensor_pair,ProductCalculation.pair_fst_comp,Laws.comp_id]
    | inr hb =>
      obtain ⟨b,rfl⟩ := hb
      rw [terminalExchange_middle]
      simp only [Laws.assoc,TerminalFold.into_before,TerminalFold.join_shift,
        TerminalFold.split_shift,terminalCross,
        ProductCalculation.tensor_pair,
        ProductCalculation.pair_fst_comp,ProductCalculation.pair_snd_comp,Laws.comp_id]
  | inr hb =>
    obtain ⟨b,rfl⟩ := hb
    cases b with
    | here =>
      rw [terminalExchange_last]
      simp only [Laws.assoc,TerminalFold.into_last,TerminalFold.out_last,
        TerminalFold.split_before,terminalCross,
        ProductCalculation.tensor_pair,ProductCalculation.pair_snd,
        ProductCalculation.pair_fst_comp,Laws.comp_id]
    | there b => cases b

theorem terminalCross_inverse (F A I : NormalForm P) :
    comp (terminalCross F A I) (terminalCross F I A) = id (.conj (.conj F A) I) := by
  simp only [terminalCross,ProductCalculation.pair_pre,ProductCalculation.pair_fst,
    ProductCalculation.pair_snd,ProductCalculation.pair_fst_comp]
  apply Reduced.conj_ext
  · rw [ProductCalculation.pair_fst,Laws.id_comp]
    apply Reduced.conj_ext
    · rw [ProductCalculation.pair_fst]
    · rw [ProductCalculation.pair_snd]
  · rw [ProductCalculation.pair_snd,Laws.id_comp]

theorem terminalExchange_out (F : List (NormalForm P)) (A : NormalForm P) (I : List (NormalForm P)) :
    comp ((terminalExchange F A I).arrow .conj)
      (comp (TerminalFold.out (F++I) A)
        (tensor .conj (ofTerm (append .conj F I).invTerm) (id A))) =
      comp (ofTerm (append .conj (F++[A]) I).invTerm)
        (comp (tensor .conj (TerminalFold.out F A) (id (ante I)))
          (terminalCross (ante F) A (ante I))) := by
  rw [terminalExchange_arrow]
  simp only [Laws.assoc]
  rw [← Laws.assoc (TerminalFold.into (F++I) A),TerminalFold.into_out,Laws.id_comp,
    Laws.tensor_comp,(append .conj F I).to_inv,Laws.id_comp,Laws.tensor_id,Laws.comp_id]

theorem terminalExchange_inverse_out (F : List (NormalForm P)) (A : NormalForm P)
    (I : List (NormalForm P)) :
    comp ((terminalExchange F A I).inverse.arrow .conj)
      (comp (ofTerm (append .conj (F++[A]) I).invTerm)
        (tensor .conj (TerminalFold.out F A) (id (ante I)))) =
      comp (TerminalFold.out (F++I) A)
        (comp (tensor .conj (ofTerm (append .conj F I).invTerm) (id A))
          (terminalCross (ante F) (ante I) A)) := by
  let e := terminalExchange F A I
  apply cancel_left _ _ (e.arrow .conj) (e.inverse.arrow .conj) (e.inverse_arrow .conj)
  rw [← Laws.assoc]
  have he := e.arrow_inverse .conj
  dsimp only [side,category] at he
  erw [he]
  rw [Laws.id_comp]
  have ht := congrArg (fun v => comp v (terminalCross (ante F) (ante I) A))
    (terminalExchange_out F A I)
  simpa only [e,Laws.assoc,terminalCross_inverse,Laws.comp_id] using ht.symm

theorem terminal_child_into (F : List (NormalForm P)) (A : NormalForm P)
    (I : List (NormalForm P)) :
    comp (tensor .conj (ofTerm (append .conj F I).toTerm) (id A))
      (comp (TerminalFold.into (F++I) A)
        (comp ((terminalExchange F A I).inverse.arrow .conj)
          (ofTerm (append .conj (F++[A]) I).invTerm))) =
      comp (terminalCross (ante F) (ante I) A)
        (tensor .conj (TerminalFold.into F A) (id (ante I))) := by
  have hi : comp (tensor .conj (TerminalFold.out F A) (id (ante I)))
      (tensor .conj (TerminalFold.into F A) (id (ante I))) =
      id (.conj (ante (F++[A])) (ante I)) := by
    rw [Laws.tensor_comp,TerminalFold.out_into,Laws.id_comp,Laws.tensor_id]
  apply cancel_right _ _ (tensor .conj (TerminalFold.out F A) (id (ante I)))
    (tensor .conj (TerminalFold.into F A) (id (ante I))) hi
  simp only [Laws.assoc]
  rw [terminalExchange_inverse_out]
  rw [← Laws.assoc (TerminalFold.into (F++I) A),TerminalFold.into_out,Laws.id_comp]
  rw [← Laws.assoc (tensor .conj (ofTerm (append .conj F I).toTerm) (id A)),
    Laws.tensor_comp,(append .conj F I).to_inv,Laws.id_comp,Laws.tensor_id,Laws.id_comp]
  rw [Laws.tensor_comp,TerminalFold.into_out,Laws.id_comp,Laws.tensor_id,Laws.comp_id]

end DosenPetric.Reduced.Gentzen.BlockedLeftDisj
