module

public import DosenPetric.PresentationSyntax

@[expose] public section

set_option autoImplicit false

namespace DosenPetric.Presentation

universe u

/-- The letterless formulas of the inherited positive language, p.121. -/
inductive Constant {P : Type u} : Formula P → Prop where
  | top : Constant .top
  | bot : Constant .bot
  | conj {A B} : Constant A → Constant B → Constant (.conj A B)
  | disj {A B} : Constant A → Constant B → Constant (.disj A B)

open Term

/-- Defining equation schemas of E(B), pp.316–317, expanded through
E(DL_top,bot), E(L_top,bot), E(DS), E(MS), and E(I^neg_top,bot).
No faithfulness equation or relation-kernel equality is a generator. -/
inductive Equation {P : Type u} : {A B : Formula P} → Term P A B → Term P A B → Prop where
  /-- (cat 1), p.332 -/
  | id_comp {A B} (f : Term P A B) : Equation
      (comp (id A) f)
      f
  /-- (cat 1), p.332 -/
  | comp_id {A B} (f : Term P A B) : Equation
      (comp f (id B))
      f
  /-- (cat 2), p.332 -/
  | assoc {A B C D} (f : Term P A B) (g : Term P B C) (h : Term P C D) : Equation
      (comp (comp f g) h)
      (comp f (comp g h))
  /-- (xi 1), p.332 -/
  | tensor_id (o : Op) (A B : Formula P) : Equation
      (tensor o (id A) (id B))
      (id (o.formula A B))
  /-- (xi 2), p.332 -/
  | tensor_comp (o : Op) {A B C D E F} (f : Term P A C) (g : Term P B D) (h : Term P C E) (k : Term P D F) : Equation
      (comp (tensor o f g) (tensor o h k))
      (tensor o (comp f h) (comp g k))
  /-- (bR nat), p.332 -/
  | assocR_nat (o : Op) {A B C D E F} (f : Term P A D) (g : Term P B E) (h : Term P C F) : Equation
      (comp (assocR o A B C) (tensor o (tensor o f g) h))
      (comp (tensor o f (tensor o g h)) (assocR o D E F))
  /-- (bL nat), p.332 -/
  | assocL_nat (o : Op) {A B C D E F} (f : Term P A D) (g : Term P B E) (h : Term P C F) : Equation
      (comp (assocL o A B C) (tensor o f (tensor o g h)))
      (comp (tensor o (tensor o f g) h) (assocL o D E F))
  /-- (b b), p.333 -/
  | assocR_L (o : Op) (A B C : Formula P) : Equation
      (comp (assocR o A B C) (assocL o A B C))
      (id (o.formula A (o.formula B C)))
  /-- (b b), p.333 -/
  | assocL_R (o : Op) (A B C : Formula P) : Equation
      (comp (assocL o A B C) (assocR o A B C))
      (id (o.formula (o.formula A B) C))
  /-- (b 5), p.89; list p.333 -/
  | pentagon (o : Op) (A B C D : Formula P) : Equation
      (comp (assocR o A B (o.formula C D)) (assocR o (o.formula A B) C D))
      (comp (tensor o (id A) (assocR o B C D)) (comp (assocR o A (o.formula B C) D) (tensor o (assocR o A B C) (id D))))
  /-- (c nat), p.333; disjunctive indices reversed -/
  | swap_nat (o : Op) {A B D E} (f : Term P A D) (g : Term P B E) : Equation
      (comp (swap o A B) (tensor o g f))
      (comp (tensor o f g) (swap o D E))
  /-- (c c), p.107; list p.334 -/
  | swap_swap (o : Op) (A B : Formula P) : Equation
      (comp (swap o A B) (swap o B A))
      (id (o.formula A B))
  /-- (b c), p.107; list p.334 -/
  | hexagon (o : Op) (A B C : Formula P) : Equation
      (swap o A (o.formula B C))
      (comp (assocR o A B C) (comp (tensor o (swap o A B) (id C)) (comp (assocL o B A C) (comp (tensor o (id B) (swap o A C)) (assocR o B C A)))))
  /-- (delta/sigma nat), pp.332–333 -/
  | rightOut_nat (o : Op) {A D} (f : Term P A D) : Equation
      (comp (rightOut o A) f)
      (comp (tensor o f (id o.unit)) (rightOut o D))
  /-- (delta/sigma nat), pp.332–333 -/
  | rightIn_nat (o : Op) {A D} (f : Term P A D) : Equation
      (comp (rightIn o A) (tensor o f (id o.unit)))
      (comp f (rightIn o D))
  /-- (delta delta)/(sigma sigma), p.101 -/
  | rightOut_In (o : Op) (A : Formula P) : Equation
      (comp (rightOut o A) (rightIn o A))
      (id (o.formula A o.unit))
  /-- (delta delta)/(sigma sigma), p.101 -/
  | rightIn_Out (o : Op) (A : Formula P) : Equation
      (comp (rightIn o A) (rightOut o A))
      (id A)
  /-- (delta/sigma nat), pp.332–333 -/
  | leftOut_nat (o : Op) {A D} (f : Term P A D) : Equation
      (comp (leftOut o A) f)
      (comp (tensor o (id o.unit) f) (leftOut o D))
  /-- (delta/sigma nat), pp.332–333 -/
  | leftIn_nat (o : Op) {A D} (f : Term P A D) : Equation
      (comp (leftIn o A) (tensor o (id o.unit) f))
      (comp f (leftIn o D))
  /-- (delta delta)/(sigma sigma), p.101 -/
  | leftOut_In (o : Op) (A : Formula P) : Equation
      (comp (leftOut o A) (leftIn o A))
      (id (o.formula o.unit A))
  /-- (delta delta)/(sigma sigma), p.101 -/
  | leftIn_Out (o : Op) (A : Formula P) : Equation
      (comp (leftIn o A) (leftOut o A))
      (id A)
  /-- (b delta sigma), p.101 -/
  | triangle (o : Op) (A C : Formula P) : Equation
      (assocR o A o.unit C)
      (comp (tensor o (id A) (leftOut o C)) (tensor o (rightIn o A) (id C)))
  /-- (w nat), p.333 -/
  | diag_nat {A D} (f : Term P A D) : Equation
      (comp (diag A) (tensor .conj f f))
      (comp f (diag D))
  /-- (w nat), p.333 -/
  | codiag_nat {A D} (f : Term P A D) : Equation
      (comp (tensor .disj f f) (codiag D))
      (comp (codiag A) f)
  /-- (k1 nat), p.333 -/
  | fst_nat {A B D E} (f : Term P A D) (g : Term P B E) : Equation
      (comp (fst A B) f)
      (comp (tensor .conj f g) (fst D E))
  /-- (k1 nat), p.333; disjunctive indices translated -/
  | inl_nat {A B D E} (f : Term P A D) (g : Term P B E) : Equation
      (comp (inl A B) (tensor .disj f g))
      (comp f (inl D E))
  /-- (k2 nat), p.333 -/
  | snd_nat {A B D E} (f : Term P A D) (g : Term P B E) : Equation
      (comp (snd A B) g)
      (comp (tensor .conj f g) (snd D E))
  /-- (k2 nat), p.333; disjunctive indices translated -/
  | inr_nat {A B D E} (f : Term P A D) (g : Term P B E) : Equation
      (comp (inr A B) (tensor .disj f g))
      (comp g (inr D E))
  /-- (b w), p.186 -/
  | diag_assoc (A : Formula P) : Equation
      (comp (diag A) (comp (tensor .conj (id A) (diag A)) (assocR .conj A A A)))
      (comp (diag A) (tensor .conj (diag A) (id A)))
  /-- (b w), dual p.186; list p.336 -/
  | codiag_assoc (A : Formula P) : Equation
      (comp (assocL .disj A A A) (comp (tensor .disj (id A) (codiag A)) (codiag A)))
      (comp (tensor .disj (codiag A) (id A)) (codiag A))
  /-- (c w), p.186 -/
  | diag_swap (A : Formula P) : Equation
      (comp (diag A) (swap .conj A A))
      (diag A)
  /-- (c w), dual p.186; list p.336 -/
  | codiag_swap (A : Formula P) : Equation
      (comp (swap .disj A A) (codiag A))
      (codiag A)
  /-- (b c w), p.186 -/
  | diag_tensor (A B : Formula P) : Equation
      (diag (.conj A B))
      (comp (tensor .conj (diag A) (diag B)) (medial .conj A A B B))
  /-- (b c w), dual p.186; list p.336 -/
  | codiag_tensor (A B : Formula P) : Equation
      (codiag (.disj A B))
      (comp (medial .disj A B A B) (tensor .disj (codiag A) (codiag B)))
  /-- (b k), p.186 -/
  | fst_assoc (A B C : Formula P) : Equation
      (comp (assocR .conj A B C) (tensor .conj (fst A B) (id C)))
      (tensor .conj (id A) (snd B C))
  /-- (b k), dual p.186; list p.336 -/
  | inl_assoc (A B C : Formula P) : Equation
      (comp (tensor .disj (inl A B) (id C)) (assocL .disj A B C))
      (tensor .disj (id A) (inr B C))
  /-- (c k), p.186 -/
  | snd_swap (A B : Formula P) : Equation
      (snd A B)
      (comp (swap .conj A B) (fst B A))
  /-- (c k), dual p.186; list p.336 -/
  | inr_swap (A B : Formula P) : Equation
      (inr A B)
      (comp (inl B A) (swap .disj B A))
  /-- (w k), p.186 -/
  | diag_fst (A : Formula P) : Equation
      (comp (diag A) (fst A A))
      (id A)
  /-- (w k), dual p.186; list p.336 -/
  | inl_codiag (A : Formula P) : Equation
      (comp (inl A A) (codiag A))
      (id A)
  /-- (w k), p.186 -/
  | diag_snd (A : Formula P) : Equation
      (comp (diag A) (snd A A))
      (id A)
  /-- (w k), dual p.186; list p.336 -/
  | inr_codiag (A : Formula P) : Equation
      (comp (inr A A) (codiag A))
      (id A)
  /-- (k delta), p.191 -/
  | fst_top (A : Formula P) : Equation
      (fst A .top)
      (rightOut .conj A)
  /-- (k delta), dual p.191; list p.338 -/
  | inl_bot (A : Formula P) : Equation
      (inl A .bot)
      (rightIn .disj A)
  /-- (c bottom)/(c top), p.121, inherited by p.207 -/
  | constant_swap (o : Op) (C : Formula P) (h : Constant C) : Equation
      (swap o C C)
      (id (o.formula C C))
  /-- (dL nat), p.333 -/
  | dist_nat {A B C D E F} (f : Term P A D) (g : Term P B E) (h : Term P C F) : Equation
      (comp (dist A B C) (tensor .disj (tensor .conj f g) h))
      (comp (tensor .conj f (tensor .disj g h)) (dist D E F))
  /-- (dR nat), p.333, dR defined by p.145 -/
  | distRight_nat {A B C D E F} (f : Term P A D) (g : Term P B E) (h : Term P C F) : Equation
      (comp (distRight A B C) (tensor .disj f (tensor .conj g h)))
      (comp (tensor .conj (tensor .disj f g) h) (distRight D E F))
  /-- (dL and), p.132 -/
  | dist_conj (A B C D : Formula P) : Equation
      (dist (.conj A B) C D)
      (comp (assocL .conj A B (.disj C D)) (comp (tensor .conj (id A) (dist B C D)) (comp (dist A (.conj B C) D) (tensor .disj (assocR .conj A B C) (id D)))))
  /-- (dL or), p.132 -/
  | dist_disj (A B C D : Formula P) : Equation
      (dist A B (.disj C D))
      (comp (tensor .conj (id A) (assocR .disj B C D)) (comp (dist A (.disj B C) D) (comp (tensor .disj (dist A B C) (id D)) (assocL .disj (.conj A B) C D))))
  /-- (dR and), p.132 -/
  | distRight_conj (A B C D : Formula P) : Equation
      (distRight A B (.conj C D))
      (comp (assocR .conj (.disj A B) C D) (comp (tensor .conj (distRight A B C) (id D)) (comp (distRight A (.conj B C) D) (tensor .disj (id A) (assocL .conj B C D)))))
  /-- (dR or), p.132 -/
  | distRight_disj (A B C D : Formula P) : Equation
      (distRight (.disj A B) C D)
      (comp (tensor .conj (assocL .disj A B C) (id D)) (comp (distRight A (.disj B C) D) (comp (tensor .disj (id A) (distRight B C D)) (assocR .disj A B (.conj C D)))))
  /-- (d b and), p.132 -/
  | dist_b_conj (A B C D : Formula P) : Equation
      (comp (tensor .conj (dist A B C) (id D)) (distRight (.conj A B) C D))
      (comp (assocL .conj A (.disj B C) D) (comp (tensor .conj (id A) (distRight B C D)) (dist A B (.conj C D))))
  /-- (d b or), p.132 -/
  | dist_b_disj (A B C D : Formula P) : Equation
      (comp (dist (.disj A B) C D) (tensor .disj (distRight A B C) (id D)))
      (comp (distRight A B (.disj C D)) (comp (tensor .disj (id A) (dist B C D)) (assocR .disj A (.conj B C) D)))
  /-- (m nat), p.333 -/
  | mix_nat {A B D E} (f : Term P A D) (g : Term P B E) : Equation
      (comp (mix A B) (tensor .disj f g))
      (comp (tensor .conj f g) (mix D E))
  /-- (b m), section 8.2; list p.336 -/
  | mix_assoc (A B C : Formula P) : Equation
      (comp (assocR .conj A B C) (comp (mix (.conj A B) C) (tensor .disj (mix A B) (id C))))
      (comp (tensor .conj (id A) (mix B C)) (comp (mix A (.disj B C)) (assocR .disj A B C)))
  /-- (c m), section 8.4; list p.336 -/
  | mix_swap (A B : Formula P) : Equation
      (comp (swap .conj A B) (mix B A))
      (comp (mix A B) (swap .disj A B))
  /-- (w m), p.219 -/
  | diag_mix_codiag (A : Formula P) : Equation
      (comp (diag A) (comp (mix A A) (codiag A)))
      (id A)
  /-- (d k and), p.234 -/
  | dist_snd (A B C : Formula P) : Equation
      (snd A (.disj B C))
      (comp (dist A B C) (tensor .disj (snd A B) (id C)))
  /-- (d k or), p.234 -/
  | dist_inl (A B C : Formula P) : Equation
      (inl (.conj A B) C)
      (comp (tensor .conj (id A) (inl B C)) (dist A B C))
  /-- (d m), p.234 -/
  | dist_mix (A B C : Formula P) : Equation
      (mix A C)
      (comp (tensor .conj (id A) (inr B C)) (comp (dist A B C) (tensor .disj (fst A B) (id C))))
  /-- (0I), p.288, inherited p.317 -/
  | zero_law {A B} (f g : Term P A B) : Equation
      (comp (zero A) f)
      (comp g (zero B))
  /-- n-r/rho isomorphism equations, pp.310,312 -/
  | dnOut_in (A : Formula P) : Equation
      (comp (dnOut A) (dnIn A))
      (id (.neg (.neg A)))
  /-- n-r/rho isomorphism equations, pp.310,312 -/
  | dnOut_out (A : Formula P) : Equation
      (comp (dnIn A) (dnOut A))
      (id A)
  /-- n-r/rho isomorphism equations, pp.310,312 -/
  | dmConjOut_in (A B : Formula P) : Equation
      (comp (dmConjOut A B) (dmConjIn A B))
      (id (.neg (.conj A B)))
  /-- n-r/rho isomorphism equations, pp.310,312 -/
  | dmConjOut_out (A B : Formula P) : Equation
      (comp (dmConjIn A B) (dmConjOut A B))
      (id (.disj (.neg A) (.neg B)))
  /-- n-r/rho isomorphism equations, pp.310,312 -/
  | dmDisjOut_in (A B : Formula P) : Equation
      (comp (dmDisjOut A B) (dmDisjIn A B))
      (id (.neg (.disj A B)))
  /-- n-r/rho isomorphism equations, pp.310,312 -/
  | dmDisjOut_out (A B : Formula P) : Equation
      (comp (dmDisjIn A B) (dmDisjOut A B))
      (id (.conj (.neg A) (.neg B)))
  /-- n-r/rho isomorphism equations, pp.310,312 -/
  | negTopOut_in  : Equation
      (comp (negTopOut) (negTopIn))
      (id (.neg .top))
  /-- n-r/rho isomorphism equations, pp.310,312 -/
  | negTopOut_out  : Equation
      (comp (negTopIn) (negTopOut))
      (id .bot)
  /-- n-r/rho isomorphism equations, pp.310,312 -/
  | negBotOut_in  : Equation
      (comp (negBotOut) (negBotIn))
      (id (.neg .bot))
  /-- n-r/rho isomorphism equations, pp.310,312 -/
  | negBotOut_out  : Equation
      (comp (negBotIn) (negBotOut))
      (id .top)

/-- Equational derivations: equivalence closure, operation congruence, and the
published schemas. Uniform substitution is proved admissible separately. -/
inductive Derives {P : Type u} : {A B : Formula P} → Term P A B → Term P A B → Prop where
  | refl {A B} (f : Term P A B) : Derives f f
  | symm {A B} {f g : Term P A B} : Derives f g → Derives g f
  | trans {A B} {f g h : Term P A B} : Derives f g → Derives g h → Derives f h
  | comp {A B C} {f f' : Term P A B} {g g' : Term P B C} :
      Derives f f' → Derives g g' → Derives (comp f g) (comp f' g')
  | tensor (o : Op) {A B C D} {f f' : Term P A C} {g g' : Term P B D} :
      Derives f f' → Derives g g' → Derives (tensor o f g) (tensor o f' g')
  | equation {A B} {f g : Term P A B} : Equation f g → Derives f g

end DosenPetric.Presentation
