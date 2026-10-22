module

public import DosenPetric.ReducedCategory
public import DosenPetric.CartesianFromDiagonal

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced
universe u
variable {P : Type u}

def assocR (o : Op) (A B C : NormalForm P) :
    Hom (o.formula A (o.formula B C)) (o.formula (o.formula A B) C) := ofTerm (.assocR o A B C)
def assocL (o : Op) (A B C : NormalForm P) :
    Hom (o.formula (o.formula A B) C) (o.formula A (o.formula B C)) := ofTerm (.assocL o A B C)
def swap (o : Op) (A B : NormalForm P) : Hom (o.formula A B) (o.formula B A) := ofTerm (.swap o A B)
def diag (A : NormalForm P) : Hom A (.conj A A) := ofTerm (.diag A)
def codiag (A : NormalForm P) : Hom (.disj A A) A := ofTerm (.codiag A)
def fst (A B : NormalForm P) : Hom (.conj A B) A := ofTerm (.fst A B)
def snd (A B : NormalForm P) : Hom (.conj A B) B := ofTerm (.snd A B)
def inl (A B : NormalForm P) : Hom A (.disj A B) := ofTerm (.inl A B)
def inr (A B : NormalForm P) : Hom B (.disj A B) := ofTerm (.inr A B)
def rightOut (o : Op) (A : NormalForm P) : Hom (o.formula A o.unit) A := ofTerm (.rightOut o A)
def rightIn (o : Op) (A : NormalForm P) : Hom A (o.formula A o.unit) := ofTerm (.rightIn o A)
def leftOut (o : Op) (A : NormalForm P) : Hom (o.formula o.unit A) A := ofTerm (.leftOut o A)
def leftIn (o : Op) (A : NormalForm P) : Hom A (o.formula o.unit A) := ofTerm (.leftIn o A)
def mix (A B : NormalForm P) : Hom (.conj A B) (.disj A B) := ofTerm (.mix A B)
def dist (A B C : NormalForm P) : Hom (.conj A (.disj B C)) (.disj (.conj A B) C) := ofTerm (.dist A B C)
def zero (A : NormalForm P) : Hom A A := ofTerm (.zero A)
def distRight (A B C : NormalForm P) : Hom (.conj (.disj A B) C) (.disj A (.conj B C)) :=
  ofTerm (.distRight A B C)
def medial (o : Op) (A B C D : NormalForm P) :
    Hom (o.formula (o.formula A B) (o.formula C D)) (o.formula (o.formula A C) (o.formula B D)) :=
  ofTerm (.medial o A B C D)

def pair {X A B : NormalForm P} (f : Hom X A) (g : Hom X B) : Hom X (.conj A B) :=
  comp (diag X) (tensor .conj f g)
def copair {A B X : NormalForm P} (f : Hom A X) (g : Hom B X) : Hom (.disj A B) X :=
  comp (tensor .disj f g) (codiag X)
def toTop (A : NormalForm P) : Hom A .top := comp (rightIn .conj A) (snd A .top)
def fromBot (A : NormalForm P) : Hom .bot A := comp (inr A .bot) (rightOut .disj A)
namespace Laws

/-- (cat 1), p.332 on equivalence classes. -/
theorem id_comp {A B : NormalForm P} (f : Hom (P := P) A B) :
    ((comp (id A) f) : Hom (P := P) _ _) =
    f := by
  induction f using Quotient.inductionOn with | h f =>
  exact equation (Equation.id_comp f)

/-- (cat 1), p.332 on equivalence classes. -/
theorem comp_id {A B : NormalForm P} (f : Hom (P := P) A B) :
    ((comp f (id B)) : Hom (P := P) _ _) =
    f := by
  induction f using Quotient.inductionOn with | h f =>
  exact equation (Equation.comp_id f)

/-- (cat 2), p.332 on equivalence classes. -/
theorem assoc {A B C D : NormalForm P} (f : Hom (P := P) A B) (g : Hom (P := P) B C) (h : Hom (P := P) C D) :
    ((comp (comp f g) h) : Hom (P := P) _ _) =
    (comp f (comp g h)) := by
  induction f using Quotient.inductionOn with | h f =>
  induction g using Quotient.inductionOn with | h g =>
  induction h using Quotient.inductionOn with | h h =>
  exact equation (Equation.assoc f g h)

/-- (xi 1), p.332 on equivalence classes. -/
theorem tensor_id (o : Op) (A B : NormalForm P) :
    ((tensor o (id A) (id B)) : Hom (P := P) _ _) =
    (id (o.formula A B)) := by
  exact equation (Equation.tensor_id o A B)

/-- (xi 2), p.332 on equivalence classes. -/
theorem tensor_comp (o : Op) {A B C D E F : NormalForm P} (f : Hom (P := P) A C) (g : Hom (P := P) B D) (h : Hom (P := P) C E) (k : Hom (P := P) D F) :
    ((comp (tensor o f g) (tensor o h k)) : Hom (P := P) _ _) =
    (tensor o (comp f h) (comp g k)) := by
  induction f using Quotient.inductionOn with | h f =>
  induction g using Quotient.inductionOn with | h g =>
  induction h using Quotient.inductionOn with | h h =>
  induction k using Quotient.inductionOn with | h k =>
  exact equation (Equation.tensor_comp o f g h k)

/-- (bR nat), p.332 on equivalence classes. -/
theorem assocR_nat (o : Op) {A B C D E F : NormalForm P} (f : Hom (P := P) A D) (g : Hom (P := P) B E) (h : Hom (P := P) C F) :
    ((comp (assocR o A B C) (tensor o (tensor o f g) h)) : Hom (P := P) _ _) =
    (comp (tensor o f (tensor o g h)) (assocR o D E F)) := by
  induction f using Quotient.inductionOn with | h f =>
  induction g using Quotient.inductionOn with | h g =>
  induction h using Quotient.inductionOn with | h h =>
  exact equation (Equation.assocR_nat o f g h)

/-- (bL nat), p.332 on equivalence classes. -/
theorem assocL_nat (o : Op) {A B C D E F : NormalForm P} (f : Hom (P := P) A D) (g : Hom (P := P) B E) (h : Hom (P := P) C F) :
    ((comp (assocL o A B C) (tensor o f (tensor o g h))) : Hom (P := P) _ _) =
    (comp (tensor o (tensor o f g) h) (assocL o D E F)) := by
  induction f using Quotient.inductionOn with | h f =>
  induction g using Quotient.inductionOn with | h g =>
  induction h using Quotient.inductionOn with | h h =>
  exact equation (Equation.assocL_nat o f g h)

/-- (b b), p.333 on equivalence classes. -/
theorem assocR_L (o : Op) (A B C : NormalForm P) :
    ((comp (assocR o A B C) (assocL o A B C)) : Hom (P := P) _ _) =
    (id (o.formula A (o.formula B C))) := by
  exact equation (Equation.assocR_L o A B C)

/-- (b b), p.333 on equivalence classes. -/
theorem assocL_R (o : Op) (A B C : NormalForm P) :
    ((comp (assocL o A B C) (assocR o A B C)) : Hom (P := P) _ _) =
    (id (o.formula (o.formula A B) C)) := by
  exact equation (Equation.assocL_R o A B C)

/-- (b 5), p.89; list p.333 on equivalence classes. -/
theorem pentagon (o : Op) (A B C D : NormalForm P) :
    ((comp (assocR o A B (o.formula C D)) (assocR o (o.formula A B) C D)) : Hom (P := P) _ _) =
    (comp (tensor o (id A) (assocR o B C D)) (comp (assocR o A (o.formula B C) D) (tensor o (assocR o A B C) (id D)))) := by
  exact equation (Equation.pentagon o A B C D)

/-- (c nat), p.333; disjunctive indices reversed on equivalence classes. -/
theorem swap_nat (o : Op) {A B D E : NormalForm P} (f : Hom (P := P) A D) (g : Hom (P := P) B E) :
    ((comp (swap o A B) (tensor o g f)) : Hom (P := P) _ _) =
    (comp (tensor o f g) (swap o D E)) := by
  induction f using Quotient.inductionOn with | h f =>
  induction g using Quotient.inductionOn with | h g =>
  exact equation (Equation.swap_nat o f g)

/-- (c c), p.107; list p.334 on equivalence classes. -/
theorem swap_swap (o : Op) (A B : NormalForm P) :
    ((comp (swap o A B) (swap o B A)) : Hom (P := P) _ _) =
    (id (o.formula A B)) := by
  exact equation (Equation.swap_swap o A B)

/-- (b c), p.107; list p.334 on equivalence classes. -/
theorem hexagon (o : Op) (A B C : NormalForm P) :
    ((swap o A (o.formula B C)) : Hom (P := P) _ _) =
    (comp (assocR o A B C) (comp (tensor o (swap o A B) (id C)) (comp (assocL o B A C) (comp (tensor o (id B) (swap o A C)) (assocR o B C A))))) := by
  exact equation (Equation.hexagon o A B C)

/-- (delta/sigma nat), pp.332–333 on equivalence classes. -/
theorem rightOut_nat (o : Op) {A D : NormalForm P} (f : Hom (P := P) A D) :
    ((comp (rightOut o A) f) : Hom (P := P) _ _) =
    (comp (tensor o f (id o.unit)) (rightOut o D)) := by
  induction f using Quotient.inductionOn with | h f =>
  exact equation (Equation.rightOut_nat o f)

/-- (delta/sigma nat), pp.332–333 on equivalence classes. -/
theorem rightIn_nat (o : Op) {A D : NormalForm P} (f : Hom (P := P) A D) :
    ((comp (rightIn o A) (tensor o f (id o.unit))) : Hom (P := P) _ _) =
    (comp f (rightIn o D)) := by
  induction f using Quotient.inductionOn with | h f =>
  exact equation (Equation.rightIn_nat o f)

/-- (delta delta)/(sigma sigma), p.101 on equivalence classes. -/
theorem rightOut_In (o : Op) (A : NormalForm P) :
    ((comp (rightOut o A) (rightIn o A)) : Hom (P := P) _ _) =
    (id (o.formula A o.unit)) := by
  exact equation (Equation.rightOut_In o A)

/-- (delta delta)/(sigma sigma), p.101 on equivalence classes. -/
theorem rightIn_Out (o : Op) (A : NormalForm P) :
    ((comp (rightIn o A) (rightOut o A)) : Hom (P := P) _ _) =
    (id A) := by
  exact equation (Equation.rightIn_Out o A)

/-- (delta/sigma nat), pp.332–333 on equivalence classes. -/
theorem leftOut_nat (o : Op) {A D : NormalForm P} (f : Hom (P := P) A D) :
    ((comp (leftOut o A) f) : Hom (P := P) _ _) =
    (comp (tensor o (id o.unit) f) (leftOut o D)) := by
  induction f using Quotient.inductionOn with | h f =>
  exact equation (Equation.leftOut_nat o f)

/-- (delta/sigma nat), pp.332–333 on equivalence classes. -/
theorem leftIn_nat (o : Op) {A D : NormalForm P} (f : Hom (P := P) A D) :
    ((comp (leftIn o A) (tensor o (id o.unit) f)) : Hom (P := P) _ _) =
    (comp f (leftIn o D)) := by
  induction f using Quotient.inductionOn with | h f =>
  exact equation (Equation.leftIn_nat o f)

/-- (delta delta)/(sigma sigma), p.101 on equivalence classes. -/
theorem leftOut_In (o : Op) (A : NormalForm P) :
    ((comp (leftOut o A) (leftIn o A)) : Hom (P := P) _ _) =
    (id (o.formula o.unit A)) := by
  exact equation (Equation.leftOut_In o A)

/-- (delta delta)/(sigma sigma), p.101 on equivalence classes. -/
theorem leftIn_Out (o : Op) (A : NormalForm P) :
    ((comp (leftIn o A) (leftOut o A)) : Hom (P := P) _ _) =
    (id A) := by
  exact equation (Equation.leftIn_Out o A)

/-- (b delta sigma), p.101 on equivalence classes. -/
theorem triangle (o : Op) (A C : NormalForm P) :
    ((assocR o A o.unit C) : Hom (P := P) _ _) =
    (comp (tensor o (id A) (leftOut o C)) (tensor o (rightIn o A) (id C))) := by
  exact equation (Equation.triangle o A C)

/-- (w nat), p.333 on equivalence classes. -/
theorem diag_nat {A D : NormalForm P} (f : Hom (P := P) A D) :
    ((comp (diag A) (tensor .conj f f)) : Hom (P := P) _ _) =
    (comp f (diag D)) := by
  induction f using Quotient.inductionOn with | h f =>
  exact equation (Equation.diag_nat f)

/-- (w nat), p.333 on equivalence classes. -/
theorem codiag_nat {A D : NormalForm P} (f : Hom (P := P) A D) :
    ((comp (tensor .disj f f) (codiag D)) : Hom (P := P) _ _) =
    (comp (codiag A) f) := by
  induction f using Quotient.inductionOn with | h f =>
  exact equation (Equation.codiag_nat f)

/-- (k1 nat), p.333 on equivalence classes. -/
theorem fst_nat {A B D E : NormalForm P} (f : Hom (P := P) A D) (g : Hom (P := P) B E) :
    ((comp (fst A B) f) : Hom (P := P) _ _) =
    (comp (tensor .conj f g) (fst D E)) := by
  induction f using Quotient.inductionOn with | h f =>
  induction g using Quotient.inductionOn with | h g =>
  exact equation (Equation.fst_nat f g)

/-- (k1 nat), p.333; disjunctive indices translated on equivalence classes. -/
theorem inl_nat {A B D E : NormalForm P} (f : Hom (P := P) A D) (g : Hom (P := P) B E) :
    ((comp (inl A B) (tensor .disj f g)) : Hom (P := P) _ _) =
    (comp f (inl D E)) := by
  induction f using Quotient.inductionOn with | h f =>
  induction g using Quotient.inductionOn with | h g =>
  exact equation (Equation.inl_nat f g)

/-- (k2 nat), p.333 on equivalence classes. -/
theorem snd_nat {A B D E : NormalForm P} (f : Hom (P := P) A D) (g : Hom (P := P) B E) :
    ((comp (snd A B) g) : Hom (P := P) _ _) =
    (comp (tensor .conj f g) (snd D E)) := by
  induction f using Quotient.inductionOn with | h f =>
  induction g using Quotient.inductionOn with | h g =>
  exact equation (Equation.snd_nat f g)

/-- (k2 nat), p.333; disjunctive indices translated on equivalence classes. -/
theorem inr_nat {A B D E : NormalForm P} (f : Hom (P := P) A D) (g : Hom (P := P) B E) :
    ((comp (inr A B) (tensor .disj f g)) : Hom (P := P) _ _) =
    (comp g (inr D E)) := by
  induction f using Quotient.inductionOn with | h f =>
  induction g using Quotient.inductionOn with | h g =>
  exact equation (Equation.inr_nat f g)

/-- (b w), p.186 on equivalence classes. -/
theorem diag_assoc (A : NormalForm P) :
    ((comp (diag A) (comp (tensor .conj (id A) (diag A)) (assocR .conj A A A))) : Hom (P := P) _ _) =
    (comp (diag A) (tensor .conj (diag A) (id A))) := by
  exact equation (Equation.diag_assoc A)

/-- (b w), dual p.186; list p.336 on equivalence classes. -/
theorem codiag_assoc (A : NormalForm P) :
    ((comp (assocL .disj A A A) (comp (tensor .disj (id A) (codiag A)) (codiag A))) : Hom (P := P) _ _) =
    (comp (tensor .disj (codiag A) (id A)) (codiag A)) := by
  exact equation (Equation.codiag_assoc A)

/-- (c w), p.186 on equivalence classes. -/
theorem diag_swap (A : NormalForm P) :
    ((comp (diag A) (swap .conj A A)) : Hom (P := P) _ _) =
    (diag A) := by
  exact equation (Equation.diag_swap A)

/-- (c w), dual p.186; list p.336 on equivalence classes. -/
theorem codiag_swap (A : NormalForm P) :
    ((comp (swap .disj A A) (codiag A)) : Hom (P := P) _ _) =
    (codiag A) := by
  exact equation (Equation.codiag_swap A)

/-- (b c w), p.186 on equivalence classes. -/
theorem diag_tensor (A B : NormalForm P) :
    ((diag (.conj A B)) : Hom (P := P) _ _) =
    (comp (tensor .conj (diag A) (diag B)) (medial .conj A A B B)) := by
  exact equation (Equation.diag_tensor A B)

/-- (b c w), dual p.186; list p.336 on equivalence classes. -/
theorem codiag_tensor (A B : NormalForm P) :
    ((codiag (.disj A B)) : Hom (P := P) _ _) =
    (comp (medial .disj A B A B) (tensor .disj (codiag A) (codiag B))) := by
  exact equation (Equation.codiag_tensor A B)

/-- (b k), p.186 on equivalence classes. -/
theorem fst_assoc (A B C : NormalForm P) :
    ((comp (assocR .conj A B C) (tensor .conj (fst A B) (id C))) : Hom (P := P) _ _) =
    (tensor .conj (id A) (snd B C)) := by
  exact equation (Equation.fst_assoc A B C)

/-- (b k), dual p.186; list p.336 on equivalence classes. -/
theorem inl_assoc (A B C : NormalForm P) :
    ((comp (tensor .disj (inl A B) (id C)) (assocL .disj A B C)) : Hom (P := P) _ _) =
    (tensor .disj (id A) (inr B C)) := by
  exact equation (Equation.inl_assoc A B C)

/-- (c k), p.186 on equivalence classes. -/
theorem snd_swap (A B : NormalForm P) :
    ((snd A B) : Hom (P := P) _ _) =
    (comp (swap .conj A B) (fst B A)) := by
  exact equation (Equation.snd_swap A B)

/-- (c k), dual p.186; list p.336 on equivalence classes. -/
theorem inr_swap (A B : NormalForm P) :
    ((inr A B) : Hom (P := P) _ _) =
    (comp (inl B A) (swap .disj B A)) := by
  exact equation (Equation.inr_swap A B)

/-- (w k), p.186 on equivalence classes. -/
theorem diag_fst (A : NormalForm P) :
    ((comp (diag A) (fst A A)) : Hom (P := P) _ _) =
    (id A) := by
  exact equation (Equation.diag_fst A)

/-- (w k), dual p.186; list p.336 on equivalence classes. -/
theorem inl_codiag (A : NormalForm P) :
    ((comp (inl A A) (codiag A)) : Hom (P := P) _ _) =
    (id A) := by
  exact equation (Equation.inl_codiag A)

/-- (w k), p.186 on equivalence classes. -/
theorem diag_snd (A : NormalForm P) :
    ((comp (diag A) (snd A A)) : Hom (P := P) _ _) =
    (id A) := by
  exact equation (Equation.diag_snd A)

/-- (w k), dual p.186; list p.336 on equivalence classes. -/
theorem inr_codiag (A : NormalForm P) :
    ((comp (inr A A) (codiag A)) : Hom (P := P) _ _) =
    (id A) := by
  exact equation (Equation.inr_codiag A)

/-- (k delta), p.191 on equivalence classes. -/
theorem fst_top (A : NormalForm P) :
    ((fst A .top) : Hom (P := P) _ _) =
    (rightOut .conj A) := by
  exact equation (Equation.fst_top A)

/-- (k delta), dual p.191; list p.338 on equivalence classes. -/
theorem inl_bot (A : NormalForm P) :
    ((inl A .bot) : Hom (P := P) _ _) =
    (rightIn .disj A) := by
  exact equation (Equation.inl_bot A)

/-- (c bottom)/(c top), p.121, inherited by p.207 on equivalence classes. -/
theorem constant_swap (o : Op) (C : NormalForm P) (h : Constant C) :
    ((swap o C C) : Hom (P := P) _ _) =
    (id (o.formula C C)) := by
  exact equation (Equation.constant_swap o C h)

/-- (dL nat), p.333 on equivalence classes. -/
theorem dist_nat {A B C D E F : NormalForm P} (f : Hom (P := P) A D) (g : Hom (P := P) B E) (h : Hom (P := P) C F) :
    ((comp (dist A B C) (tensor .disj (tensor .conj f g) h)) : Hom (P := P) _ _) =
    (comp (tensor .conj f (tensor .disj g h)) (dist D E F)) := by
  induction f using Quotient.inductionOn with | h f =>
  induction g using Quotient.inductionOn with | h g =>
  induction h using Quotient.inductionOn with | h h =>
  exact equation (Equation.dist_nat f g h)

/-- (dR nat), p.333, dR defined by p.145 on equivalence classes. -/
theorem distRight_nat {A B C D E F : NormalForm P} (f : Hom (P := P) A D) (g : Hom (P := P) B E) (h : Hom (P := P) C F) :
    ((comp (distRight A B C) (tensor .disj f (tensor .conj g h))) : Hom (P := P) _ _) =
    (comp (tensor .conj (tensor .disj f g) h) (distRight D E F)) := by
  induction f using Quotient.inductionOn with | h f =>
  induction g using Quotient.inductionOn with | h g =>
  induction h using Quotient.inductionOn with | h h =>
  exact equation (Equation.distRight_nat f g h)

/-- (dL and), p.132 on equivalence classes. -/
theorem dist_conj (A B C D : NormalForm P) :
    ((dist (.conj A B) C D) : Hom (P := P) _ _) =
    (comp (assocL .conj A B (.disj C D)) (comp (tensor .conj (id A) (dist B C D)) (comp (dist A (.conj B C) D) (tensor .disj (assocR .conj A B C) (id D))))) := by
  exact equation (Equation.dist_conj A B C D)

/-- (dL or), p.132 on equivalence classes. -/
theorem dist_disj (A B C D : NormalForm P) :
    ((dist A B (.disj C D)) : Hom (P := P) _ _) =
    (comp (tensor .conj (id A) (assocR .disj B C D)) (comp (dist A (.disj B C) D) (comp (tensor .disj (dist A B C) (id D)) (assocL .disj (.conj A B) C D)))) := by
  exact equation (Equation.dist_disj A B C D)

/-- (dR and), p.132 on equivalence classes. -/
theorem distRight_conj (A B C D : NormalForm P) :
    ((distRight A B (.conj C D)) : Hom (P := P) _ _) =
    (comp (assocR .conj (.disj A B) C D) (comp (tensor .conj (distRight A B C) (id D)) (comp (distRight A (.conj B C) D) (tensor .disj (id A) (assocL .conj B C D))))) := by
  exact equation (Equation.distRight_conj A B C D)

/-- (dR or), p.132 on equivalence classes. -/
theorem distRight_disj (A B C D : NormalForm P) :
    ((distRight (.disj A B) C D) : Hom (P := P) _ _) =
    (comp (tensor .conj (assocL .disj A B C) (id D)) (comp (distRight A (.disj B C) D) (comp (tensor .disj (id A) (distRight B C D)) (assocR .disj A B (.conj C D))))) := by
  exact equation (Equation.distRight_disj A B C D)

/-- (d b and), p.132 on equivalence classes. -/
theorem dist_b_conj (A B C D : NormalForm P) :
    ((comp (tensor .conj (dist A B C) (id D)) (distRight (.conj A B) C D)) : Hom (P := P) _ _) =
    (comp (assocL .conj A (.disj B C) D) (comp (tensor .conj (id A) (distRight B C D)) (dist A B (.conj C D)))) := by
  exact equation (Equation.dist_b_conj A B C D)

/-- (d b or), p.132 on equivalence classes. -/
theorem dist_b_disj (A B C D : NormalForm P) :
    ((comp (dist (.disj A B) C D) (tensor .disj (distRight A B C) (id D))) : Hom (P := P) _ _) =
    (comp (distRight A B (.disj C D)) (comp (tensor .disj (id A) (dist B C D)) (assocR .disj A (.conj B C) D))) := by
  exact equation (Equation.dist_b_disj A B C D)

/-- (m nat), p.333 on equivalence classes. -/
theorem mix_nat {A B D E : NormalForm P} (f : Hom (P := P) A D) (g : Hom (P := P) B E) :
    ((comp (mix A B) (tensor .disj f g)) : Hom (P := P) _ _) =
    (comp (tensor .conj f g) (mix D E)) := by
  induction f using Quotient.inductionOn with | h f =>
  induction g using Quotient.inductionOn with | h g =>
  exact equation (Equation.mix_nat f g)

/-- (b m), section 8.2; list p.336 on equivalence classes. -/
theorem mix_assoc (A B C : NormalForm P) :
    ((comp (assocR .conj A B C) (comp (mix (.conj A B) C) (tensor .disj (mix A B) (id C)))) : Hom (P := P) _ _) =
    (comp (tensor .conj (id A) (mix B C)) (comp (mix A (.disj B C)) (assocR .disj A B C))) := by
  exact equation (Equation.mix_assoc A B C)

/-- (c m), section 8.4; list p.336 on equivalence classes. -/
theorem mix_swap (A B : NormalForm P) :
    ((comp (swap .conj A B) (mix B A)) : Hom (P := P) _ _) =
    (comp (mix A B) (swap .disj A B)) := by
  exact equation (Equation.mix_swap A B)

/-- (w m), p.219 on equivalence classes. -/
theorem diag_mix_codiag (A : NormalForm P) :
    ((comp (diag A) (comp (mix A A) (codiag A))) : Hom (P := P) _ _) =
    (id A) := by
  exact equation (Equation.diag_mix_codiag A)

/-- (d k and), p.234 on equivalence classes. -/
theorem dist_snd (A B C : NormalForm P) :
    ((snd A (.disj B C)) : Hom (P := P) _ _) =
    (comp (dist A B C) (tensor .disj (snd A B) (id C))) := by
  exact equation (Equation.dist_snd A B C)

/-- (d k or), p.234 on equivalence classes. -/
theorem dist_inl (A B C : NormalForm P) :
    ((inl (.conj A B) C) : Hom (P := P) _ _) =
    (comp (tensor .conj (id A) (inl B C)) (dist A B C)) := by
  exact equation (Equation.dist_inl A B C)

/-- (d m), p.234 on equivalence classes. -/
theorem dist_mix (A B C : NormalForm P) :
    ((mix A C) : Hom (P := P) _ _) =
    (comp (tensor .conj (id A) (inr B C)) (comp (dist A B C) (tensor .disj (fst A B) (id C)))) := by
  exact equation (Equation.dist_mix A B C)

/-- (0I), p.288, inherited p.317 on equivalence classes. -/
theorem zero_law {A B : NormalForm P} (f g : Hom (P := P) A B) :
    ((comp (zero A) f) : Hom (P := P) _ _) =
    (comp g (zero B)) := by
  induction f using Quotient.inductionOn with | h f =>
  induction g using Quotient.inductionOn with | h g =>
  exact equation (Equation.zero_law f g)

end Laws
end DosenPetric.Reduced
