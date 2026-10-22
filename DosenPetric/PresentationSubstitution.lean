module

public import DosenPetric.PresentationCategory

@[expose] public section

set_option autoImplicit false

namespace DosenPetric.Presentation

universe u v

namespace Term

/-- Uniform formula substitution acts on the whole arrow and both endpoints. -/
def subst {P : Type u} {Q : Type v} (σ : P → Formula Q) :
    {A B : Formula P} → Term P A B → Term Q (A.subst σ) (B.subst σ)
  | _, _, .id A => .id (A.subst σ)
  | _, _, .comp f g => .comp (subst σ f) (subst σ g)
  | _, _, .tensor .conj f g => .tensor .conj (subst σ f) (subst σ g)
  | _, _, .tensor .disj f g => .tensor .disj (subst σ f) (subst σ g)
  | _, _, .assocR .conj A B C => .assocR .conj (A.subst σ) (B.subst σ) (C.subst σ)
  | _, _, .assocR .disj A B C => .assocR .disj (A.subst σ) (B.subst σ) (C.subst σ)
  | _, _, .assocL .conj A B C => .assocL .conj (A.subst σ) (B.subst σ) (C.subst σ)
  | _, _, .assocL .disj A B C => .assocL .disj (A.subst σ) (B.subst σ) (C.subst σ)
  | _, _, .swap .conj A B => .swap .conj (A.subst σ) (B.subst σ)
  | _, _, .swap .disj A B => .swap .disj (A.subst σ) (B.subst σ)
  | _, _, .diag A => .diag (A.subst σ)
  | _, _, .codiag A => .codiag (A.subst σ)
  | _, _, .fst A B => .fst (A.subst σ) (B.subst σ)
  | _, _, .snd A B => .snd (A.subst σ) (B.subst σ)
  | _, _, .inl A B => .inl (A.subst σ) (B.subst σ)
  | _, _, .inr A B => .inr (A.subst σ) (B.subst σ)
  | _, _, .rightOut .conj A => .rightOut .conj (A.subst σ)
  | _, _, .rightOut .disj A => .rightOut .disj (A.subst σ)
  | _, _, .rightIn .conj A => .rightIn .conj (A.subst σ)
  | _, _, .rightIn .disj A => .rightIn .disj (A.subst σ)
  | _, _, .leftOut .conj A => .leftOut .conj (A.subst σ)
  | _, _, .leftOut .disj A => .leftOut .disj (A.subst σ)
  | _, _, .leftIn .conj A => .leftIn .conj (A.subst σ)
  | _, _, .leftIn .disj A => .leftIn .disj (A.subst σ)
  | _, _, .mix A B => .mix (A.subst σ) (B.subst σ)
  | _, _, .dist A B C => .dist (A.subst σ) (B.subst σ) (C.subst σ)
  | _, _, .zero A => .zero (A.subst σ)
  | _, _, .dnOut A => .dnOut (A.subst σ)
  | _, _, .dnIn A => .dnIn (A.subst σ)
  | _, _, .dmConjOut A B => .dmConjOut (A.subst σ) (B.subst σ)
  | _, _, .dmConjIn A B => .dmConjIn (A.subst σ) (B.subst σ)
  | _, _, .dmDisjOut A B => .dmDisjOut (A.subst σ) (B.subst σ)
  | _, _, .dmDisjIn A B => .dmDisjIn (A.subst σ) (B.subst σ)
  | _, _, .negTopOut => .negTopOut
  | _, _, .negTopIn => .negTopIn
  | _, _, .negBotOut => .negBotOut
  | _, _, .negBotIn => .negBotIn
  | _, _, .excludedMiddle A => .excludedMiddle (A.subst σ)
  | _, _, .contradiction A => .contradiction (A.subst σ)

end Term

variable {P : Type u} {Q : Type v}

theorem Constant.subst (σ : P → Formula Q) {C : Formula P} (h : Constant C) :
    Constant (C.subst σ) := by
  induction h with
  | top => exact .top
  | bot => exact .bot
  | conj _ _ ih ih' => exact .conj ih ih'
  | disj _ _ ih ih' => exact .disj ih ih'

/-- Every defining schema is stable under uniform substitution, including its
positive-letterless side condition. This is the source rule (su). -/
theorem Equation.subst (σ : P → Formula Q) {A B : Formula P} {f g : Term P A B}
    (e : Equation f g) : Equation (f.subst σ) (g.subst σ) := by
  cases e with
  | @id_comp A B f =>
    simp only [Term.subst]
    exact Equation.id_comp _
  | @comp_id A B f =>
    simp only [Term.subst]
    exact Equation.comp_id _
  | @assoc A B C D f g h =>
    simp only [Term.subst]
    exact Equation.assoc _ _ _
  | @tensor_id o A B =>
    cases o <;>
    simp only [Term.subst]
    all_goals exact Equation.tensor_id _ _ _
  | @tensor_comp o A B C D E F f g h k =>
    cases o <;>
    simp only [Term.subst]
    all_goals exact Equation.tensor_comp _ _ _ _ _
  | @assocR_nat o A B C D E F f g h =>
    cases o <;>
    simp only [Term.subst]
    all_goals exact Equation.assocR_nat _ _ _ _
  | @assocL_nat o A B C D E F f g h =>
    cases o <;>
    simp only [Term.subst]
    all_goals exact Equation.assocL_nat _ _ _ _
  | @assocR_L o A B C =>
    cases o <;>
    simp only [Term.subst]
    all_goals exact Equation.assocR_L _ _ _ _
  | @assocL_R o A B C =>
    cases o <;>
    simp only [Term.subst]
    all_goals exact Equation.assocL_R _ _ _ _
  | @pentagon o A B C D =>
    cases o <;>
    simp only [Term.subst]
    all_goals exact Equation.pentagon _ _ _ _ _
  | @swap_nat o A B D E f g =>
    cases o <;>
    simp only [Term.subst]
    all_goals exact Equation.swap_nat _ _ _
  | @swap_swap o A B =>
    cases o <;>
    simp only [Term.subst]
    all_goals exact Equation.swap_swap _ _ _
  | @hexagon o A B C =>
    cases o <;>
    simp only [Term.subst]
    all_goals exact Equation.hexagon _ _ _ _
  | @rightOut_nat o A D f =>
    cases o <;>
    simp only [Term.subst]
    all_goals exact Equation.rightOut_nat _ _
  | @rightIn_nat o A D f =>
    cases o <;>
    simp only [Term.subst]
    all_goals exact Equation.rightIn_nat _ _
  | @rightOut_In o A =>
    cases o <;>
    simp only [Term.subst]
    all_goals exact Equation.rightOut_In _ _
  | @rightIn_Out o A =>
    cases o <;>
    simp only [Term.subst]
    all_goals exact Equation.rightIn_Out _ _
  | @leftOut_nat o A D f =>
    cases o <;>
    simp only [Term.subst]
    all_goals exact Equation.leftOut_nat _ _
  | @leftIn_nat o A D f =>
    cases o <;>
    simp only [Term.subst]
    all_goals exact Equation.leftIn_nat _ _
  | @leftOut_In o A =>
    cases o <;>
    simp only [Term.subst]
    all_goals exact Equation.leftOut_In _ _
  | @leftIn_Out o A =>
    cases o <;>
    simp only [Term.subst]
    all_goals exact Equation.leftIn_Out _ _
  | @triangle o A C =>
    cases o <;>
    simp only [Term.subst]
    all_goals exact Equation.triangle _ _ _
  | @diag_nat A D f =>
    simp only [Term.subst]
    exact Equation.diag_nat _
  | @codiag_nat A D f =>
    simp only [Term.subst]
    exact Equation.codiag_nat _
  | @fst_nat A B D E f g =>
    simp only [Term.subst]
    exact Equation.fst_nat _ _
  | @inl_nat A B D E f g =>
    simp only [Term.subst]
    exact Equation.inl_nat _ _
  | @snd_nat A B D E f g =>
    simp only [Term.subst]
    exact Equation.snd_nat _ _
  | @inr_nat A B D E f g =>
    simp only [Term.subst]
    exact Equation.inr_nat _ _
  | @diag_assoc A =>
    simp only [Term.subst]
    exact Equation.diag_assoc _
  | @codiag_assoc A =>
    simp only [Term.subst]
    exact Equation.codiag_assoc _
  | @diag_swap A =>
    simp only [Term.subst]
    exact Equation.diag_swap _
  | @codiag_swap A =>
    simp only [Term.subst]
    exact Equation.codiag_swap _
  | @diag_tensor A B =>
    simp only [Term.subst]
    exact Equation.diag_tensor _ _
  | @codiag_tensor A B =>
    simp only [Term.subst]
    exact Equation.codiag_tensor _ _
  | @fst_assoc A B C =>
    simp only [Term.subst]
    exact Equation.fst_assoc _ _ _
  | @inl_assoc A B C =>
    simp only [Term.subst]
    exact Equation.inl_assoc _ _ _
  | @snd_swap A B =>
    simp only [Term.subst]
    exact Equation.snd_swap _ _
  | @inr_swap A B =>
    simp only [Term.subst]
    exact Equation.inr_swap _ _
  | @diag_fst A =>
    simp only [Term.subst]
    exact Equation.diag_fst _
  | @inl_codiag A =>
    simp only [Term.subst]
    exact Equation.inl_codiag _
  | @diag_snd A =>
    simp only [Term.subst]
    exact Equation.diag_snd _
  | @inr_codiag A =>
    simp only [Term.subst]
    exact Equation.inr_codiag _
  | @fst_top A =>
    simp only [Term.subst]
    exact Equation.fst_top _
  | @inl_bot A =>
    simp only [Term.subst]
    exact Equation.inl_bot _
  | @constant_swap o C h =>
    cases o <;>
    simp only [Term.subst]
    all_goals exact Equation.constant_swap _ _ (h.subst σ)
  | @dist_nat A B C D E F f g h =>
    simp only [Term.subst]
    exact Equation.dist_nat _ _ _
  | @distRight_nat A B C D E F f g h =>
    simp only [Term.subst]
    exact Equation.distRight_nat _ _ _
  | @dist_conj A B C D =>
    simp only [Term.subst]
    exact Equation.dist_conj _ _ _ _
  | @dist_disj A B C D =>
    simp only [Term.subst]
    exact Equation.dist_disj _ _ _ _
  | @distRight_conj A B C D =>
    simp only [Term.subst]
    exact Equation.distRight_conj _ _ _ _
  | @distRight_disj A B C D =>
    simp only [Term.subst]
    exact Equation.distRight_disj _ _ _ _
  | @dist_b_conj A B C D =>
    simp only [Term.subst]
    exact Equation.dist_b_conj _ _ _ _
  | @dist_b_disj A B C D =>
    simp only [Term.subst]
    exact Equation.dist_b_disj _ _ _ _
  | @mix_nat A B D E f g =>
    simp only [Term.subst]
    exact Equation.mix_nat _ _
  | @mix_assoc A B C =>
    simp only [Term.subst]
    exact Equation.mix_assoc _ _ _
  | @mix_swap A B =>
    simp only [Term.subst]
    exact Equation.mix_swap _ _
  | @diag_mix_codiag A =>
    simp only [Term.subst]
    exact Equation.diag_mix_codiag _
  | @dist_snd A B C =>
    simp only [Term.subst]
    exact Equation.dist_snd _ _ _
  | @dist_inl A B C =>
    simp only [Term.subst]
    exact Equation.dist_inl _ _ _
  | @dist_mix A B C =>
    simp only [Term.subst]
    exact Equation.dist_mix _ _ _
  | @zero_law A B f g =>
    simp only [Term.subst]
    exact Equation.zero_law _ _
  | @dnOut_in A =>
    simp only [Term.subst]
    exact Equation.dnOut_in _
  | @dnOut_out A =>
    simp only [Term.subst]
    exact Equation.dnOut_out _
  | @dmConjOut_in A B =>
    simp only [Term.subst]
    exact Equation.dmConjOut_in _ _
  | @dmConjOut_out A B =>
    simp only [Term.subst]
    exact Equation.dmConjOut_out _ _
  | @dmDisjOut_in A B =>
    simp only [Term.subst]
    exact Equation.dmDisjOut_in _ _
  | @dmDisjOut_out A B =>
    simp only [Term.subst]
    exact Equation.dmDisjOut_out _ _
  | @negTopOut_in =>
    simp only [Term.subst]
    exact Equation.negTopOut_in
  | @negTopOut_out =>
    simp only [Term.subst]
    exact Equation.negTopOut_out
  | @negBotOut_in =>
    simp only [Term.subst]
    exact Equation.negBotOut_in
  | @negBotOut_out =>
    simp only [Term.subst]
    exact Equation.negBotOut_out

/-- Substitution respects the generated congruence; no interpretation kernel is used. -/
theorem Derives.subst (σ : P → Formula Q) {A B : Formula P} {f g : Term P A B}
    (e : Derives f g) : Derives (f.subst σ) (g.subst σ) := by
  induction e with
  | refl f => exact .refl _
  | symm _ ih => exact .symm ih
  | trans _ _ ih ih' => exact .trans ih ih'
  | comp _ _ ih ih' => exact .comp ih ih'
  | tensor o _ _ ih ih' => cases o <;> exact .tensor _ ih ih'
  | equation e => exact .equation (e.subst σ)

/-- Substitution descends to the actual equation-generated quotient. -/
def substitute (σ : P → Formula Q) {A B : Formula P} (f : Hom A B) :
    Hom (A.subst σ) (B.subst σ) :=
  Quotient.liftOn f (fun t => ofTerm (t.subst σ)) (fun _ _ e => sound (e.subst σ))

theorem substitute_id (σ : P → Formula Q) (A : Formula P) :
    substitute σ (id A) = id (A.subst σ) := rfl

theorem substitute_comp (σ : P → Formula Q) {A B C : Formula P}
    (f : Hom A B) (g : Hom B C) :
    substitute σ (comp f g) = comp (substitute σ f) (substitute σ g) := by
  induction f using Quotient.inductionOn with | h f =>
  induction g using Quotient.inductionOn with | h g => rfl

end DosenPetric.Presentation
