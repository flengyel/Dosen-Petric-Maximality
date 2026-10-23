module

public import DosenPetric.PositiveGentzenSyntax

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

/-- A right-empty append is the right unitor, after its explicit list equality. -/
def appendNil (o : Op) : (Γ : List (NormalForm P)) →
    Iso (o.formula (fold o Γ) o.unit) (fold o Γ)
  | [] => Iso.leftUnit o o.unit
  | A :: Γ => (Iso.assoc o A (fold o Γ) o.unit).trans
      (Iso.tensor o (Iso.refl A) (appendNil o Γ))

theorem appendNil_to (o : Op) (Γ : List (NormalForm P)) :
    ofTerm (appendNil o Γ).toTerm = rightOut o (fold o Γ) := by
  induction Γ with
  | nil =>
    change leftOut o o.unit = rightOut o o.unit
    rw [← swap_unit_out]
    have h : Constant (o.unit : NormalForm P) := by cases o <;> constructor
    rw [Laws.constant_swap o o.unit h, Laws.id_comp]
  | cons A Γ ih =>
    change comp (assocL o A (fold o Γ) o.unit)
      (tensor o (id A) (ofTerm (appendNil o Γ).toTerm)) = _
    rw [ih, rightOut_tensor]

theorem cut_pure {Γ : List (NormalForm P)} {B C : NormalForm P}
    (f : G P Γ [B]) (g : G P [B] [C]) :
    ofTerm (G.cut (Θ := []) (Δ := []) f g).denote =
      comp (ofTerm f.denote) (comp (rightOut .disj B)
        (comp (rightIn .conj B) (ofTerm g.denote))) := by
  change comp (leftIn .conj (ante Γ))
    (comp (tensor .conj (id .top) (ofTerm f.denote))
      (comp (dist .top B .bot)
        (comp (tensor .disj (comp (swap .conj .top B) (ofTerm g.denote)) (id .bot))
          (ofTerm (appendNil .disj [C]).toTerm)))) = _
  rw [appendNil_to, dist_top]
  simp only [Laws.assoc]
  rw [← Laws.assoc (leftIn .conj (ante Γ)), Laws.leftIn_nat]
  simp only [Laws.assoc]
  rw [← Laws.assoc (leftIn .conj (.disj B .bot)), Laws.leftIn_Out, Laws.id_comp,
    ← Laws.assoc (tensor .disj (leftIn .conj B) (id .bot)), Laws.tensor_comp, Laws.id_comp,
    ← Laws.assoc (leftIn .conj B), swap_unit_in, ← Laws.rightOut_nat]

theorem cut_single {A B C : NormalForm P}
    (f : G P [A] [B]) (g : G P [B] [C]) :
    decode (G.cut (Θ := []) (Δ := []) f g).denote =
      comp (decode f.denote) (decode g.denote) := by
  unfold decode
  rw [cut_pure]
  simp only [Laws.assoc]

theorem unit_left_right (o : Op) :
    leftOut o (o.unit : NormalForm P) = rightOut o o.unit := by
  rw [← swap_unit_out]
  have h : Constant (o.unit : NormalForm P) := by cases o <;> constructor
  rw [Laws.constant_swap o o.unit h, Laws.id_comp]

/-- Both empty output residuals of the multiplicative conjunction rule. -/
theorem mixedDisj_bot (A B : NormalForm P) :
    comp (ofTerm (Term.mixedDisj A .bot B .bot))
      (comp (tensor .disj (id (.conj A B)) (leftOut .disj .bot))
        (rightOut .disj (.conj A B))) =
      tensor .conj (rightOut .disj A) (rightOut .disj B) := by
  change comp (comp (dist (.disj A .bot) B .bot)
    (comp (tensor .disj
      (comp (swap .conj (.disj A .bot) B)
        (comp (dist B A .bot) (tensor .disj (swap .conj B A) (id .bot)))) (id .bot))
      (assocL .disj (.conj A B) .bot .bot))) _ = _
  rw [dist_bot, dist_bot]
  rw [unit_left_right .disj]
  simp only [Laws.assoc]
  rw [← Laws.assoc (assocL .disj (.conj A B) .bot .bot), rightOut_tensor]
  rw [← Laws.assoc (tensor .disj _ (id .bot)), ← Laws.rightOut_nat]
  simp only [Laws.assoc]
  rw [← Laws.assoc (rightIn .disj _), Laws.rightIn_Out, Laws.id_comp]
  rw [← Laws.rightOut_nat .disj (swap .conj B A)]
  rw [← Laws.assoc (rightIn .disj _), Laws.rightIn_Out, Laws.id_comp]
  rw [← Laws.assoc (swap .conj (.disj A .bot) B), Laws.swap_nat]
  simp only [Laws.assoc]
  rw [Laws.swap_swap, Laws.comp_id, Laws.tensor_comp, Laws.id_comp, Laws.comp_id]

end DosenPetric.Reduced.Gentzen
