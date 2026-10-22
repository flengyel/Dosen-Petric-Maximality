module

public import DosenPetric.ReducedEquations

@[expose] public section

set_option autoImplicit false

namespace DosenPetric.Reduced

universe u

namespace Term

variable {P : Type u}

def toFull : {A B : NormalForm P} → Term P A B → Presentation.Term P A.formula B.formula
  | _, _, .id A => .id A.formula
  | _, _, .comp f g => .comp f.toFull g.toFull
  | _, _, .tensor .conj f g => .tensor .conj f.toFull g.toFull
  | _, _, .tensor .disj f g => .tensor .disj f.toFull g.toFull
  | _, _, .assocR .conj A B C => .assocR .conj A.formula B.formula C.formula
  | _, _, .assocR .disj A B C => .assocR .disj A.formula B.formula C.formula
  | _, _, .assocL .conj A B C => .assocL .conj A.formula B.formula C.formula
  | _, _, .assocL .disj A B C => .assocL .disj A.formula B.formula C.formula
  | _, _, .swap .conj A B => .swap .conj A.formula B.formula
  | _, _, .swap .disj A B => .swap .disj A.formula B.formula
  | _, _, .diag A => .diag A.formula
  | _, _, .codiag A => .codiag A.formula
  | _, _, .fst A B => .fst A.formula B.formula
  | _, _, .snd A B => .snd A.formula B.formula
  | _, _, .inl A B => .inl A.formula B.formula
  | _, _, .inr A B => .inr A.formula B.formula
  | _, _, .rightOut .conj A => .rightOut .conj A.formula
  | _, _, .rightOut .disj A => .rightOut .disj A.formula
  | _, _, .rightIn .conj A => .rightIn .conj A.formula
  | _, _, .rightIn .disj A => .rightIn .disj A.formula
  | _, _, .leftOut .conj A => .leftOut .conj A.formula
  | _, _, .leftOut .disj A => .leftOut .disj A.formula
  | _, _, .leftIn .conj A => .leftIn .conj A.formula
  | _, _, .leftIn .disj A => .leftIn .disj A.formula
  | _, _, .mix A B => .mix A.formula B.formula
  | _, _, .dist A B C => .dist A.formula B.formula C.formula
  | _, _, .zero A => .zero A.formula
  | _, _, .eta p => .excludedMiddle (.var p)
  | _, _, .epsilon p => .contradiction (.var p)

end Term

variable {P : Type u}

theorem Constant.toFull {A : NormalForm P} (h : Constant A) : Presentation.Constant A.formula := by
  induction h with
  | top => exact .top
  | bot => exact .bot
  | conj _ _ ih ih' => exact .conj ih ih'
  | disj _ _ ih ih' => exact .disj ih ih'

theorem Equation.toFull {A B : NormalForm P} {f g : Term P A B} (e : Equation f g) :
    Presentation.Equation f.toFull g.toFull := by
  cases e with
  | @id_comp A B f =>
    exact Presentation.Equation.id_comp _
  | @comp_id A B f =>
    exact Presentation.Equation.comp_id _
  | @assoc A B C D f g h =>
    exact Presentation.Equation.assoc _ _ _
  | @tensor_id o A B =>
    cases o <;> exact Presentation.Equation.tensor_id _ _ _
  | @tensor_comp o A B C D E F f g h k =>
    cases o <;> exact Presentation.Equation.tensor_comp _ _ _ _ _
  | @assocR_nat o A B C D E F f g h =>
    cases o <;> exact Presentation.Equation.assocR_nat _ _ _ _
  | @assocL_nat o A B C D E F f g h =>
    cases o <;> exact Presentation.Equation.assocL_nat _ _ _ _
  | @assocR_L o A B C =>
    cases o <;> exact Presentation.Equation.assocR_L _ _ _ _
  | @assocL_R o A B C =>
    cases o <;> exact Presentation.Equation.assocL_R _ _ _ _
  | @pentagon o A B C D =>
    cases o <;> exact Presentation.Equation.pentagon _ _ _ _ _
  | @swap_nat o A B D E f g =>
    cases o <;> exact Presentation.Equation.swap_nat _ _ _
  | @swap_swap o A B =>
    cases o <;> exact Presentation.Equation.swap_swap _ _ _
  | @hexagon o A B C =>
    cases o <;> exact Presentation.Equation.hexagon _ _ _ _
  | @rightOut_nat o A D f =>
    cases o <;> exact Presentation.Equation.rightOut_nat _ _
  | @rightIn_nat o A D f =>
    cases o <;> exact Presentation.Equation.rightIn_nat _ _
  | @rightOut_In o A =>
    cases o <;> exact Presentation.Equation.rightOut_In _ _
  | @rightIn_Out o A =>
    cases o <;> exact Presentation.Equation.rightIn_Out _ _
  | @leftOut_nat o A D f =>
    cases o <;> exact Presentation.Equation.leftOut_nat _ _
  | @leftIn_nat o A D f =>
    cases o <;> exact Presentation.Equation.leftIn_nat _ _
  | @leftOut_In o A =>
    cases o <;> exact Presentation.Equation.leftOut_In _ _
  | @leftIn_Out o A =>
    cases o <;> exact Presentation.Equation.leftIn_Out _ _
  | @triangle o A C =>
    cases o <;> exact Presentation.Equation.triangle _ _ _
  | @diag_nat A D f =>
    exact Presentation.Equation.diag_nat _
  | @codiag_nat A D f =>
    exact Presentation.Equation.codiag_nat _
  | @fst_nat A B D E f g =>
    exact Presentation.Equation.fst_nat _ _
  | @inl_nat A B D E f g =>
    exact Presentation.Equation.inl_nat _ _
  | @snd_nat A B D E f g =>
    exact Presentation.Equation.snd_nat _ _
  | @inr_nat A B D E f g =>
    exact Presentation.Equation.inr_nat _ _
  | @diag_assoc A =>
    exact Presentation.Equation.diag_assoc _
  | @codiag_assoc A =>
    exact Presentation.Equation.codiag_assoc _
  | @diag_swap A =>
    exact Presentation.Equation.diag_swap _
  | @codiag_swap A =>
    exact Presentation.Equation.codiag_swap _
  | @diag_tensor A B =>
    exact Presentation.Equation.diag_tensor _ _
  | @codiag_tensor A B =>
    exact Presentation.Equation.codiag_tensor _ _
  | @fst_assoc A B C =>
    exact Presentation.Equation.fst_assoc _ _ _
  | @inl_assoc A B C =>
    exact Presentation.Equation.inl_assoc _ _ _
  | @snd_swap A B =>
    exact Presentation.Equation.snd_swap _ _
  | @inr_swap A B =>
    exact Presentation.Equation.inr_swap _ _
  | @diag_fst A =>
    exact Presentation.Equation.diag_fst _
  | @inl_codiag A =>
    exact Presentation.Equation.inl_codiag _
  | @diag_snd A =>
    exact Presentation.Equation.diag_snd _
  | @inr_codiag A =>
    exact Presentation.Equation.inr_codiag _
  | @fst_top A =>
    exact Presentation.Equation.fst_top _
  | @inl_bot A =>
    exact Presentation.Equation.inl_bot _
  | @constant_swap o C h =>
    cases o <;> exact Presentation.Equation.constant_swap _ _ h.toFull
  | @dist_nat A B C D E F f g h =>
    exact Presentation.Equation.dist_nat _ _ _
  | @distRight_nat A B C D E F f g h =>
    exact Presentation.Equation.distRight_nat _ _ _
  | @dist_conj A B C D =>
    exact Presentation.Equation.dist_conj _ _ _ _
  | @dist_disj A B C D =>
    exact Presentation.Equation.dist_disj _ _ _ _
  | @distRight_conj A B C D =>
    exact Presentation.Equation.distRight_conj _ _ _ _
  | @distRight_disj A B C D =>
    exact Presentation.Equation.distRight_disj _ _ _ _
  | @dist_b_conj A B C D =>
    exact Presentation.Equation.dist_b_conj _ _ _ _
  | @dist_b_disj A B C D =>
    exact Presentation.Equation.dist_b_disj _ _ _ _
  | @mix_nat A B D E f g =>
    exact Presentation.Equation.mix_nat _ _
  | @mix_assoc A B C =>
    exact Presentation.Equation.mix_assoc _ _ _
  | @mix_swap A B =>
    exact Presentation.Equation.mix_swap _ _
  | @diag_mix_codiag A =>
    exact Presentation.Equation.diag_mix_codiag _
  | @dist_snd A B C =>
    exact Presentation.Equation.dist_snd _ _ _
  | @dist_inl A B C =>
    exact Presentation.Equation.dist_inl _ _ _
  | @dist_mix A B C =>
    exact Presentation.Equation.dist_mix _ _ _
  | @zero_law A B f g =>
    exact Presentation.Equation.zero_law _ _

theorem Derives.toFull {A B : NormalForm P} {f g : Term P A B} (e : Derives f g) :
    Presentation.Derives f.toFull g.toFull := by
  induction e with
  | refl _ => exact .refl _
  | symm _ ih => exact .symm ih
  | trans _ _ ih ih' => exact .trans ih ih'
  | comp _ _ ih ih' => exact .comp ih ih'
  | tensor o _ _ ih ih' => cases o <;> exact .tensor _ ih ih'
  | equation e => exact .equation e.toFull

def termSetoid (A B : NormalForm P) : Setoid (Term P A B) where
  r := Derives
  iseqv := ⟨Derives.refl, Derives.symm, Derives.trans⟩

abbrev Hom (A B : NormalForm P) := Quotient (termSetoid A B)

def ofTerm {A B : NormalForm P} (t : Term P A B) : Hom A B := Quotient.mk _ t

theorem sound {A B : NormalForm P} {s t : Term P A B} (h : Derives s t) :
    ofTerm s = ofTerm t := Quotient.sound h

theorem equation {A B : NormalForm P} {s t : Term P A B} (h : Equation s t) :
    ofTerm s = ofTerm t := sound (.equation h)

def id (A : NormalForm P) : Hom A A := ofTerm (.id A)

def comp {A B C : NormalForm P} (f : Hom A B) (g : Hom B C) : Hom A C :=
  Quotient.liftOn₂ f g (fun f g => ofTerm (.comp f g))
    (fun _ _ _ _ hf hg => Quotient.sound (.comp hf hg))

def tensor (o : Op) {A B C D : NormalForm P} (f : Hom A C) (g : Hom B D) :
    Hom (o.formula A B) (o.formula C D) :=
  Quotient.liftOn₂ f g (fun f g => ofTerm (.tensor o f g))
    (fun _ _ _ _ hf hg => Quotient.sound (.tensor o hf hg))

def category (P : Type u) : Category (NormalForm P) where
  Hom := Hom
  id := id
  comp := comp
  id_comp f := by
    induction f using Quotient.inductionOn with | h f =>
    exact Quotient.sound (.equation (.id_comp f))
  comp_id f := by
    induction f using Quotient.inductionOn with | h f =>
    exact Quotient.sound (.equation (.comp_id f))
  assoc f g h := by
    induction f using Quotient.inductionOn with | h f =>
    induction g using Quotient.inductionOn with | h g =>
    induction h using Quotient.inductionOn with | h h =>
    exact Quotient.sound (.equation (.assoc f g h))

def inclusion {A B : NormalForm P} (f : Hom A B) : Presentation.Hom A.formula B.formula :=
  Quotient.liftOn f (fun t => Presentation.ofTerm t.toFull)
    (fun _ _ h => Presentation.sound h.toFull)

theorem inclusion_ofTerm {A B : NormalForm P} (t : Term P A B) :
    inclusion (ofTerm t) = Presentation.ofTerm t.toFull := rfl

theorem inclusion_id (A : NormalForm P) : inclusion (id A) = Presentation.id A.formula := rfl

theorem inclusion_comp {A B C : NormalForm P} (f : Hom A B) (g : Hom B C) :
    inclusion (comp f g) = Presentation.comp (inclusion f) (inclusion g) := by
  induction f using Quotient.inductionOn with | h f =>
  induction g using Quotient.inductionOn with | h g => rfl

theorem inclusion_tensor_conj {A B C D : NormalForm P} (f : Hom A C) (g : Hom B D) :
    inclusion (tensor .conj f g) = Presentation.tensor .conj (inclusion f) (inclusion g) := by
  induction f using Quotient.inductionOn with | h f =>
  induction g using Quotient.inductionOn with | h g => rfl

theorem inclusion_tensor_disj {A B C D : NormalForm P} (f : Hom A C) (g : Hom B D) :
    inclusion (tensor .disj f g) = Presentation.tensor .disj (inclusion f) (inclusion g) := by
  induction f using Quotient.inductionOn with | h f =>
  induction g using Quotient.inductionOn with | h g => rfl

end DosenPetric.Reduced
