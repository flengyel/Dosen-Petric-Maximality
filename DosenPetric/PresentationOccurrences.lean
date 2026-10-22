module

public import DosenPetric.PresentationZero
public import DosenPetric.Relations

@[expose] public section

set_option autoImplicit false

namespace DosenPetric.Presentation

universe u

namespace Occurrence

open Relations

def unassoc {X Y Z : Type} : Sum (Sum X Y) Z → Sum X (Sum Y Z)
  | .inl (.inl x) => .inl x
  | .inl (.inr y) => .inr (.inl y)
  | .inr z => .inr (.inr z)

def exchange {X Y : Type} : Sum X Y → Sum Y X
  | .inl x => .inr x
  | .inr y => .inl y

def dropRight {X : Type} : Sum X Empty → X
  | .inl x => x
  | .inr e => Empty.elim e

def dropLeft {X : Type} : Sum Empty X → X
  | .inl e => Empty.elim e
  | .inr x => x

theorem sumMap_graph {X Y X' Y' : Type} (f : X → X') (g : Y → Y') :
    sumMap (graph f) (graph g) = graph (Sum.map f g) := by
  funext x y
  apply propext
  cases x <;> cases y <;> simp [sumMap, graph, Sum.map]

end Occurrence

namespace Term

open Relations Occurrence

/-- The source relation assignment uses tagged positions. It does not define
syntactic equality; its descent requires a separate proof for every equation. -/
def relation {P : Type u} : {A B : Formula P} → Term P A B → Rel A.Occ B.Occ
  | _, _, .id A => graph _root_.id
  | _, _, .comp f g => Relations.comp (relation f) (relation g)
  | _, _, .tensor .conj f g => sumMap (relation f) (relation g)
  | _, _, .tensor .disj f g => sumMap (relation f) (relation g)
  | _, _, .assocR .conj A B C => graph reassoc
  | _, _, .assocR .disj A B C => graph reassoc
  | _, _, .assocL .conj A B C => graph unassoc
  | _, _, .assocL .disj A B C => graph unassoc
  | _, _, .swap .conj A B => graph exchange
  | _, _, .swap .disj A B => graph exchange
  | _, _, .diag A => Relations.pair (graph _root_.id) (graph _root_.id)
  | _, _, .codiag A => Relations.copair (graph _root_.id) (graph _root_.id)
  | _, _, .fst A B => fstRel
  | _, _, .snd A B => sndRel
  | _, _, .inl A B => graph Sum.inl
  | _, _, .inr A B => graph Sum.inr
  | _, _, .rightOut .conj A => graph dropRight
  | _, _, .rightOut .disj A => graph dropRight
  | _, _, .rightIn .conj A => graph Sum.inl
  | _, _, .rightIn .disj A => graph Sum.inl
  | _, _, .leftOut .conj A => graph dropLeft
  | _, _, .leftOut .disj A => graph dropLeft
  | _, _, .leftIn .conj A => graph Sum.inr
  | _, _, .leftIn .disj A => graph Sum.inr
  | _, _, .mix A B => graph _root_.id
  | _, _, .dist A B C => graph reassoc
  | _, _, .zero A => empty
  | _, _, .dnOut A => graph _root_.id
  | _, _, .dnIn A => graph _root_.id
  | _, _, .dmConjOut A B => graph _root_.id
  | _, _, .dmConjIn A B => graph _root_.id
  | _, _, .dmDisjOut A B => graph _root_.id
  | _, _, .dmDisjIn A B => graph _root_.id
  | _, _, .negTopOut => graph _root_.id
  | _, _, .negTopIn => graph _root_.id
  | _, _, .negBotOut => graph _root_.id
  | _, _, .negBotIn => graph _root_.id
  | _, _, .excludedMiddle A => empty
  | _, _, .contradiction A => empty

end Term

variable {P : Type u}

theorem Constant.no_occ {A : Formula P} (h : Constant A) (x : A.Occ) : False := by
  induction h with
  | top => exact Empty.elim x
  | bot => exact Empty.elim x
  | conj _ _ ih ih' => cases x with | inl x => exact ih x | inr x => exact ih' x
  | disj _ _ ih ih' => cases x with | inl x => exact ih x | inr x => exact ih' x

attribute [local simp] Term.relation Term.medial Relations.comp Relations.graph
  Relations.sumMap Relations.pair Relations.copair Relations.fstRel Relations.sndRel
  Relations.reassoc Relations.empty Occurrence.unassoc Occurrence.exchange
  Occurrence.dropRight Occurrence.dropLeft Sum.exists
  Occurrence.sumMap_graph Relations.graph_comp Relations.id_comp Relations.comp_id
  Relations.empty_comp Relations.comp_empty Sum.map

/-- The derived right distributor has the inverse reassociation occurrence map. -/
theorem Term.relation_distRight (A B C : Formula P) :
    (Term.distRight A B C).relation = Relations.graph Occurrence.unassoc := by
  funext x y
  apply propext
  rcases x with (x | x) | x <;> rcases y with y | (y | y) <;>
    simp [Term.distRight]

attribute [local simp 2000] Term.relation_distRight

/-- (cat 1), p.332: relation preservation for this schema. -/
private theorem equation_relation_id_comp {A B : Formula P} (f : Term P A B) :
    ((Term.comp (Term.id A) f) : Term P _ _).relation =
    (f : Term P _ _).relation := by
  exact Relations.id_comp _

/-- (cat 1), p.332: relation preservation for this schema. -/
private theorem equation_relation_comp_id {A B : Formula P} (f : Term P A B) :
    ((Term.comp f (Term.id B)) : Term P _ _).relation =
    (f : Term P _ _).relation := by
  exact Relations.comp_id _

/-- (cat 2), p.332: relation preservation for this schema. -/
private theorem equation_relation_assoc {A B C D : Formula P} (f : Term P A B) (g : Term P B C) (h : Term P C D) :
    ((Term.comp (Term.comp f g) h) : Term P _ _).relation =
    ((Term.comp f (Term.comp g h)) : Term P _ _).relation := by
  exact Relations.comp_assoc _ _ _

/-- (xi 1), p.332: relation preservation for this schema. -/
private theorem equation_relation_tensor_id (o : Op) (A B : Formula P) :
    ((Term.tensor o (Term.id A) (Term.id B)) : Term P _ _).relation =
    ((Term.id (o.formula A B)) : Term P _ _).relation := by
  cases o <;>
  funext x y
  all_goals apply propext
  all_goals rcases x with (x | x) <;>
  all_goals rcases y with (y | y) <;>
  all_goals first | exact Empty.elim (by assumption) | simp

/-- (xi 2), p.332: relation preservation for this schema. -/
private theorem equation_relation_tensor_comp (o : Op) {A B C D E F : Formula P} (f : Term P A C) (g : Term P B D) (h : Term P C E) (k : Term P D F) :
    ((Term.comp (Term.tensor o f g) (Term.tensor o h k)) : Term P _ _).relation =
    ((Term.tensor o (Term.comp f h) (Term.comp g k)) : Term P _ _).relation := by
  cases o <;>
  funext x y
  all_goals apply propext
  all_goals rcases x with (x | x) <;>
  all_goals rcases y with (y | y) <;>
  all_goals first | exact Empty.elim (by assumption) | simp

/-- (bR nat), p.332: relation preservation for this schema. -/
private theorem equation_relation_assocR_nat (o : Op) {A B C D E F : Formula P} (f : Term P A D) (g : Term P B E) (h : Term P C F) :
    ((Term.comp (Term.assocR o A B C) (Term.tensor o (Term.tensor o f g) h)) : Term P _ _).relation =
    ((Term.comp (Term.tensor o f (Term.tensor o g h)) (Term.assocR o D E F)) : Term P _ _).relation := by
  cases o <;>
  funext x y
  all_goals apply propext
  all_goals rcases x with (x | (x | x)) <;>
  all_goals rcases y with ((y | y) | y) <;>
  all_goals first | exact Empty.elim (by assumption) | simp

/-- (bL nat), p.332: relation preservation for this schema. -/
private theorem equation_relation_assocL_nat (o : Op) {A B C D E F : Formula P} (f : Term P A D) (g : Term P B E) (h : Term P C F) :
    ((Term.comp (Term.assocL o A B C) (Term.tensor o f (Term.tensor o g h))) : Term P _ _).relation =
    ((Term.comp (Term.tensor o (Term.tensor o f g) h) (Term.assocL o D E F)) : Term P _ _).relation := by
  cases o <;>
  funext x y
  all_goals apply propext
  all_goals rcases x with ((x | x) | x) <;>
  all_goals rcases y with (y | (y | y)) <;>
  all_goals first | exact Empty.elim (by assumption) | simp

/-- (b b), p.333: relation preservation for this schema. -/
private theorem equation_relation_assocR_L (o : Op) (A B C : Formula P) :
    ((Term.comp (Term.assocR o A B C) (Term.assocL o A B C)) : Term P _ _).relation =
    ((Term.id (o.formula A (o.formula B C))) : Term P _ _).relation := by
  cases o <;>
  funext x y
  all_goals apply propext
  all_goals rcases x with (x | (x | x)) <;>
  all_goals rcases y with (y | (y | y)) <;>
  all_goals first | exact Empty.elim (by assumption) | simp

/-- (b b), p.333: relation preservation for this schema. -/
private theorem equation_relation_assocL_R (o : Op) (A B C : Formula P) :
    ((Term.comp (Term.assocL o A B C) (Term.assocR o A B C)) : Term P _ _).relation =
    ((Term.id (o.formula (o.formula A B) C)) : Term P _ _).relation := by
  cases o <;>
  funext x y
  all_goals apply propext
  all_goals rcases x with ((x | x) | x) <;>
  all_goals rcases y with ((y | y) | y) <;>
  all_goals first | exact Empty.elim (by assumption) | simp

/-- (b 5), p.89; list p.333: relation preservation for this schema. -/
private theorem equation_relation_pentagon (o : Op) (A B C D : Formula P) :
    ((Term.comp (Term.assocR o A B (o.formula C D)) (Term.assocR o (o.formula A B) C D)) : Term P _ _).relation =
    ((Term.comp (Term.tensor o (Term.id A) (Term.assocR o B C D)) (Term.comp (Term.assocR o A (o.formula B C) D) (Term.tensor o (Term.assocR o A B C) (Term.id D)))) : Term P _ _).relation := by
  cases o <;>
  funext x y
  all_goals apply propext
  all_goals rcases x with (x | (x | (x | x))) <;>
  all_goals rcases y with (((y | y) | y) | y) <;>
  all_goals first | exact Empty.elim (by assumption) | simp

/-- (c nat), p.333; disjunctive indices reversed: relation preservation for this schema. -/
private theorem equation_relation_swap_nat (o : Op) {A B D E : Formula P} (f : Term P A D) (g : Term P B E) :
    ((Term.comp (Term.swap o A B) (Term.tensor o g f)) : Term P _ _).relation =
    ((Term.comp (Term.tensor o f g) (Term.swap o D E)) : Term P _ _).relation := by
  cases o <;>
  funext x y
  all_goals apply propext
  all_goals rcases x with (x | x) <;>
  all_goals rcases y with (y | y) <;>
  all_goals first | exact Empty.elim (by assumption) | simp

/-- (c c), p.107; list p.334: relation preservation for this schema. -/
private theorem equation_relation_swap_swap (o : Op) (A B : Formula P) :
    ((Term.comp (Term.swap o A B) (Term.swap o B A)) : Term P _ _).relation =
    ((Term.id (o.formula A B)) : Term P _ _).relation := by
  cases o <;>
  funext x y
  all_goals apply propext
  all_goals rcases x with (x | x) <;>
  all_goals rcases y with (y | y) <;>
  all_goals first | exact Empty.elim (by assumption) | simp

/-- (b c), p.107; list p.334: relation preservation for this schema. -/
private theorem equation_relation_hexagon (o : Op) (A B C : Formula P) :
    ((Term.swap o A (o.formula B C)) : Term P _ _).relation =
    ((Term.comp (Term.assocR o A B C) (Term.comp (Term.tensor o (Term.swap o A B) (Term.id C)) (Term.comp (Term.assocL o B A C) (Term.comp (Term.tensor o (Term.id B) (Term.swap o A C)) (Term.assocR o B C A))))) : Term P _ _).relation := by
  cases o <;>
  funext x y
  all_goals apply propext
  all_goals rcases x with (x | (x | x)) <;>
  all_goals rcases y with ((y | y) | y) <;>
  all_goals first | exact Empty.elim (by assumption) | simp

/-- (delta/sigma nat), pp.332–333: relation preservation for this schema. -/
private theorem equation_relation_rightOut_nat (o : Op) {A D : Formula P} (f : Term P A D) :
    ((Term.comp (Term.rightOut o A) f) : Term P _ _).relation =
    ((Term.comp (Term.tensor o f (Term.id o.unit)) (Term.rightOut o D)) : Term P _ _).relation := by
  cases o <;>
  funext x y
  all_goals apply propext
  all_goals rcases x with (x | ⟨⟩) <;>
  all_goals first | exact Empty.elim (by assumption) | simp

/-- (delta/sigma nat), pp.332–333: relation preservation for this schema. -/
private theorem equation_relation_rightIn_nat (o : Op) {A D : Formula P} (f : Term P A D) :
    ((Term.comp (Term.rightIn o A) (Term.tensor o f (Term.id o.unit))) : Term P _ _).relation =
    ((Term.comp f (Term.rightIn o D)) : Term P _ _).relation := by
  cases o <;>
  funext x y
  all_goals apply propext
  all_goals rcases y with (y | ⟨⟩) <;>
  all_goals first | exact Empty.elim (by assumption) | simp

/-- (delta delta)/(sigma sigma), p.101: relation preservation for this schema. -/
private theorem equation_relation_rightOut_In (o : Op) (A : Formula P) :
    ((Term.comp (Term.rightOut o A) (Term.rightIn o A)) : Term P _ _).relation =
    ((Term.id (o.formula A o.unit)) : Term P _ _).relation := by
  cases o <;>
  funext x y
  all_goals apply propext
  all_goals rcases x with (x | ⟨⟩) <;>
  all_goals rcases y with (y | ⟨⟩) <;>
  all_goals first | exact Empty.elim (by assumption) | simp

/-- (delta delta)/(sigma sigma), p.101: relation preservation for this schema. -/
private theorem equation_relation_rightIn_Out (o : Op) (A : Formula P) :
    ((Term.comp (Term.rightIn o A) (Term.rightOut o A)) : Term P _ _).relation =
    ((Term.id A) : Term P _ _).relation := by
  cases o <;>
  funext x y
  all_goals apply propext
  all_goals first | exact Empty.elim (by assumption) | simp

/-- (delta/sigma nat), pp.332–333: relation preservation for this schema. -/
private theorem equation_relation_leftOut_nat (o : Op) {A D : Formula P} (f : Term P A D) :
    ((Term.comp (Term.leftOut o A) f) : Term P _ _).relation =
    ((Term.comp (Term.tensor o (Term.id o.unit) f) (Term.leftOut o D)) : Term P _ _).relation := by
  cases o <;>
  funext x y
  all_goals apply propext
  all_goals rcases x with (⟨⟩ | x) <;>
  all_goals first | exact Empty.elim (by assumption) | simp

/-- (delta/sigma nat), pp.332–333: relation preservation for this schema. -/
private theorem equation_relation_leftIn_nat (o : Op) {A D : Formula P} (f : Term P A D) :
    ((Term.comp (Term.leftIn o A) (Term.tensor o (Term.id o.unit) f)) : Term P _ _).relation =
    ((Term.comp f (Term.leftIn o D)) : Term P _ _).relation := by
  cases o <;>
  funext x y
  all_goals apply propext
  all_goals rcases y with (⟨⟩ | y) <;>
  all_goals first | exact Empty.elim (by assumption) | simp

/-- (delta delta)/(sigma sigma), p.101: relation preservation for this schema. -/
private theorem equation_relation_leftOut_In (o : Op) (A : Formula P) :
    ((Term.comp (Term.leftOut o A) (Term.leftIn o A)) : Term P _ _).relation =
    ((Term.id (o.formula o.unit A)) : Term P _ _).relation := by
  cases o <;>
  funext x y
  all_goals apply propext
  all_goals rcases x with (⟨⟩ | x) <;>
  all_goals rcases y with (⟨⟩ | y) <;>
  all_goals first | exact Empty.elim (by assumption) | simp

/-- (delta delta)/(sigma sigma), p.101: relation preservation for this schema. -/
private theorem equation_relation_leftIn_Out (o : Op) (A : Formula P) :
    ((Term.comp (Term.leftIn o A) (Term.leftOut o A)) : Term P _ _).relation =
    ((Term.id A) : Term P _ _).relation := by
  cases o <;>
  funext x y
  all_goals apply propext
  all_goals first | exact Empty.elim (by assumption) | simp

/-- (b delta sigma), p.101: relation preservation for this schema. -/
private theorem equation_relation_triangle (o : Op) (A C : Formula P) :
    ((Term.assocR o A o.unit C) : Term P _ _).relation =
    ((Term.comp (Term.tensor o (Term.id A) (Term.leftOut o C)) (Term.tensor o (Term.rightIn o A) (Term.id C))) : Term P _ _).relation := by
  cases o <;>
  funext x y
  all_goals apply propext
  all_goals rcases x with (x | (⟨⟩ | x)) <;>
  all_goals rcases y with ((y | ⟨⟩) | y) <;>
  all_goals first | exact Empty.elim (by assumption) | simp

/-- (w nat), p.333: relation preservation for this schema. -/
private theorem equation_relation_diag_nat {A D : Formula P} (f : Term P A D) :
    ((Term.comp (Term.diag A) (Term.tensor .conj f f)) : Term P _ _).relation =
    ((Term.comp f (Term.diag D)) : Term P _ _).relation := by
  funext x y
  apply propext
  rcases y with (y | y) <;>
  all_goals first | exact Empty.elim (by assumption) | simp

/-- (w nat), p.333: relation preservation for this schema. -/
private theorem equation_relation_codiag_nat {A D : Formula P} (f : Term P A D) :
    ((Term.comp (Term.tensor .disj f f) (Term.codiag D)) : Term P _ _).relation =
    ((Term.comp (Term.codiag A) f) : Term P _ _).relation := by
  funext x y
  apply propext
  rcases x with (x | x) <;>
  all_goals first | exact Empty.elim (by assumption) | simp

/-- (k1 nat), p.333: relation preservation for this schema. -/
private theorem equation_relation_fst_nat {A B D E : Formula P} (f : Term P A D) (g : Term P B E) :
    ((Term.comp (Term.fst A B) f) : Term P _ _).relation =
    ((Term.comp (Term.tensor .conj f g) (Term.fst D E)) : Term P _ _).relation := by
  funext x y
  apply propext
  rcases x with (x | x) <;>
  all_goals first | exact Empty.elim (by assumption) | simp

/-- (k1 nat), p.333; disjunctive indices translated: relation preservation for this schema. -/
private theorem equation_relation_inl_nat {A B D E : Formula P} (f : Term P A D) (g : Term P B E) :
    ((Term.comp (Term.inl A B) (Term.tensor .disj f g)) : Term P _ _).relation =
    ((Term.comp f (Term.inl D E)) : Term P _ _).relation := by
  funext x y
  apply propext
  rcases y with (y | y) <;>
  all_goals first | exact Empty.elim (by assumption) | simp

/-- (k2 nat), p.333: relation preservation for this schema. -/
private theorem equation_relation_snd_nat {A B D E : Formula P} (f : Term P A D) (g : Term P B E) :
    ((Term.comp (Term.snd A B) g) : Term P _ _).relation =
    ((Term.comp (Term.tensor .conj f g) (Term.snd D E)) : Term P _ _).relation := by
  funext x y
  apply propext
  rcases x with (x | x) <;>
  all_goals first | exact Empty.elim (by assumption) | simp

/-- (k2 nat), p.333; disjunctive indices translated: relation preservation for this schema. -/
private theorem equation_relation_inr_nat {A B D E : Formula P} (f : Term P A D) (g : Term P B E) :
    ((Term.comp (Term.inr A B) (Term.tensor .disj f g)) : Term P _ _).relation =
    ((Term.comp g (Term.inr D E)) : Term P _ _).relation := by
  funext x y
  apply propext
  rcases y with (y | y) <;>
  all_goals first | exact Empty.elim (by assumption) | simp

/-- (b w), p.186: relation preservation for this schema. -/
private theorem equation_relation_diag_assoc (A : Formula P) :
    ((Term.comp (Term.diag A) (Term.comp (Term.tensor .conj (Term.id A) (Term.diag A)) (Term.assocR .conj A A A))) : Term P _ _).relation =
    ((Term.comp (Term.diag A) (Term.tensor .conj (Term.diag A) (Term.id A))) : Term P _ _).relation := by
  funext x y
  apply propext
  rcases y with ((y | y) | y) <;>
  all_goals first | exact Empty.elim (by assumption) | simp

/-- (b w), dual p.186; list p.336: relation preservation for this schema. -/
private theorem equation_relation_codiag_assoc (A : Formula P) :
    ((Term.comp (Term.assocL .disj A A A) (Term.comp (Term.tensor .disj (Term.id A) (Term.codiag A)) (Term.codiag A))) : Term P _ _).relation =
    ((Term.comp (Term.tensor .disj (Term.codiag A) (Term.id A)) (Term.codiag A)) : Term P _ _).relation := by
  funext x y
  apply propext
  rcases x with ((x | x) | x) <;>
  all_goals first | exact Empty.elim (by assumption) | simp

/-- (c w), p.186: relation preservation for this schema. -/
private theorem equation_relation_diag_swap (A : Formula P) :
    ((Term.comp (Term.diag A) (Term.swap .conj A A)) : Term P _ _).relation =
    ((Term.diag A) : Term P _ _).relation := by
  funext x y
  apply propext
  rcases y with (y | y) <;>
  all_goals first | exact Empty.elim (by assumption) | simp

/-- (c w), dual p.186; list p.336: relation preservation for this schema. -/
private theorem equation_relation_codiag_swap (A : Formula P) :
    ((Term.comp (Term.swap .disj A A) (Term.codiag A)) : Term P _ _).relation =
    ((Term.codiag A) : Term P _ _).relation := by
  funext x y
  apply propext
  rcases x with (x | x) <;>
  all_goals first | exact Empty.elim (by assumption) | simp

/-- (b c w), p.186: relation preservation for this schema. -/
private theorem equation_relation_diag_tensor (A B : Formula P) :
    ((Term.diag (.conj A B)) : Term P _ _).relation =
    ((Term.comp (Term.tensor .conj (Term.diag A) (Term.diag B)) (Term.medial .conj A A B B)) : Term P _ _).relation := by
  funext x y
  apply propext
  rcases x with (x | x) <;>
  rcases y with ((y | y) | (y | y)) <;>
  all_goals first | exact Empty.elim (by assumption) | simp

/-- (b c w), dual p.186; list p.336: relation preservation for this schema. -/
private theorem equation_relation_codiag_tensor (A B : Formula P) :
    ((Term.codiag (.disj A B)) : Term P _ _).relation =
    ((Term.comp (Term.medial .disj A B A B) (Term.tensor .disj (Term.codiag A) (Term.codiag B))) : Term P _ _).relation := by
  funext x y
  apply propext
  rcases x with ((x | x) | (x | x)) <;>
  rcases y with (y | y) <;>
  all_goals first | exact Empty.elim (by assumption) | simp

/-- (b k), p.186: relation preservation for this schema. -/
private theorem equation_relation_fst_assoc (A B C : Formula P) :
    ((Term.comp (Term.assocR .conj A B C) (Term.tensor .conj (Term.fst A B) (Term.id C))) : Term P _ _).relation =
    ((Term.tensor .conj (Term.id A) (Term.snd B C)) : Term P _ _).relation := by
  funext x y
  apply propext
  rcases x with (x | (x | x)) <;>
  rcases y with (y | y) <;>
  all_goals first | exact Empty.elim (by assumption) | simp

/-- (b k), dual p.186; list p.336: relation preservation for this schema. -/
private theorem equation_relation_inl_assoc (A B C : Formula P) :
    ((Term.comp (Term.tensor .disj (Term.inl A B) (Term.id C)) (Term.assocL .disj A B C)) : Term P _ _).relation =
    ((Term.tensor .disj (Term.id A) (Term.inr B C)) : Term P _ _).relation := by
  funext x y
  apply propext
  rcases x with (x | x) <;>
  rcases y with (y | (y | y)) <;>
  all_goals first | exact Empty.elim (by assumption) | simp

/-- (c k), p.186: relation preservation for this schema. -/
private theorem equation_relation_snd_swap (A B : Formula P) :
    ((Term.snd A B) : Term P _ _).relation =
    ((Term.comp (Term.swap .conj A B) (Term.fst B A)) : Term P _ _).relation := by
  funext x y
  apply propext
  rcases x with (x | x) <;>
  all_goals first | exact Empty.elim (by assumption) | simp

/-- (c k), dual p.186; list p.336: relation preservation for this schema. -/
private theorem equation_relation_inr_swap (A B : Formula P) :
    ((Term.inr A B) : Term P _ _).relation =
    ((Term.comp (Term.inl B A) (Term.swap .disj B A)) : Term P _ _).relation := by
  funext x y
  apply propext
  rcases y with (y | y) <;>
  all_goals first | exact Empty.elim (by assumption) | simp

/-- (w k), p.186: relation preservation for this schema. -/
private theorem equation_relation_diag_fst (A : Formula P) :
    ((Term.comp (Term.diag A) (Term.fst A A)) : Term P _ _).relation =
    ((Term.id A) : Term P _ _).relation := by
  funext x y
  apply propext
  all_goals first | exact Empty.elim (by assumption) | simp

/-- (w k), dual p.186; list p.336: relation preservation for this schema. -/
private theorem equation_relation_inl_codiag (A : Formula P) :
    ((Term.comp (Term.inl A A) (Term.codiag A)) : Term P _ _).relation =
    ((Term.id A) : Term P _ _).relation := by
  funext x y
  apply propext
  all_goals first | exact Empty.elim (by assumption) | simp

/-- (w k), p.186: relation preservation for this schema. -/
private theorem equation_relation_diag_snd (A : Formula P) :
    ((Term.comp (Term.diag A) (Term.snd A A)) : Term P _ _).relation =
    ((Term.id A) : Term P _ _).relation := by
  funext x y
  apply propext
  all_goals first | exact Empty.elim (by assumption) | simp

/-- (w k), dual p.186; list p.336: relation preservation for this schema. -/
private theorem equation_relation_inr_codiag (A : Formula P) :
    ((Term.comp (Term.inr A A) (Term.codiag A)) : Term P _ _).relation =
    ((Term.id A) : Term P _ _).relation := by
  funext x y
  apply propext
  all_goals first | exact Empty.elim (by assumption) | simp

/-- (k delta), p.191: relation preservation for this schema. -/
private theorem equation_relation_fst_top (A : Formula P) :
    ((Term.fst A .top) : Term P _ _).relation =
    ((Term.rightOut .conj A) : Term P _ _).relation := by
  funext x y
  apply propext
  rcases x with (x | ⟨⟩) <;>
  all_goals first | exact Empty.elim (by assumption) | simp

/-- (k delta), dual p.191; list p.338: relation preservation for this schema. -/
private theorem equation_relation_inl_bot (A : Formula P) :
    ((Term.inl A .bot) : Term P _ _).relation =
    ((Term.rightIn .disj A) : Term P _ _).relation := by
  funext x y
  apply propext
  rcases y with (y | ⟨⟩) <;>
  all_goals first | exact Empty.elim (by assumption) | simp

/-- (c bottom)/(c top), p.121, inherited by p.207: relation preservation for this schema. -/
private theorem equation_relation_constant_swap (o : Op) (C : Formula P) (h : Constant C) :
    ((Term.swap o C C) : Term P _ _).relation =
    ((Term.id (o.formula C C)) : Term P _ _).relation := by
  cases o <;>
  funext x y
  all_goals apply propext
  all_goals cases x with | inl x => exact False.elim (h.no_occ x) | inr x => exact False.elim (h.no_occ x)

/-- (dL nat), p.333: relation preservation for this schema. -/
private theorem equation_relation_dist_nat {A B C D E F : Formula P} (f : Term P A D) (g : Term P B E) (h : Term P C F) :
    ((Term.comp (Term.dist A B C) (Term.tensor .disj (Term.tensor .conj f g) h)) : Term P _ _).relation =
    ((Term.comp (Term.tensor .conj f (Term.tensor .disj g h)) (Term.dist D E F)) : Term P _ _).relation := by
  funext x y
  apply propext
  rcases x with (x | (x | x)) <;>
  rcases y with ((y | y) | y) <;>
  all_goals first | exact Empty.elim (by assumption) | simp

/-- (dR nat), p.333, dR defined by p.145: relation preservation for this schema. -/
private theorem equation_relation_distRight_nat {A B C D E F : Formula P} (f : Term P A D) (g : Term P B E) (h : Term P C F) :
    ((Term.comp (Term.distRight A B C) (Term.tensor .disj f (Term.tensor .conj g h))) : Term P _ _).relation =
    ((Term.comp (Term.tensor .conj (Term.tensor .disj f g) h) (Term.distRight D E F)) : Term P _ _).relation := by
  funext x y
  apply propext
  rcases x with ((x | x) | x) <;>
  rcases y with (y | (y | y)) <;>
  all_goals first | exact Empty.elim (by assumption) | simp

/-- (dL and), p.132: relation preservation for this schema. -/
private theorem equation_relation_dist_conj (A B C D : Formula P) :
    ((Term.dist (.conj A B) C D) : Term P _ _).relation =
    ((Term.comp (Term.assocL .conj A B (.disj C D)) (Term.comp (Term.tensor .conj (Term.id A) (Term.dist B C D)) (Term.comp (Term.dist A (.conj B C) D) (Term.tensor .disj (Term.assocR .conj A B C) (Term.id D))))) : Term P _ _).relation := by
  funext x y
  apply propext
  rcases x with ((x | x) | (x | x)) <;>
  rcases y with (((y | y) | y) | y) <;>
  all_goals first | exact Empty.elim (by assumption) | simp

/-- (dL or), p.132: relation preservation for this schema. -/
private theorem equation_relation_dist_disj (A B C D : Formula P) :
    ((Term.dist A B (.disj C D)) : Term P _ _).relation =
    ((Term.comp (Term.tensor .conj (Term.id A) (Term.assocR .disj B C D)) (Term.comp (Term.dist A (.disj B C) D) (Term.comp (Term.tensor .disj (Term.dist A B C) (Term.id D)) (Term.assocL .disj (.conj A B) C D)))) : Term P _ _).relation := by
  funext x y
  apply propext
  rcases x with (x | (x | (x | x))) <;>
  rcases y with ((y | y) | (y | y)) <;>
  all_goals first | exact Empty.elim (by assumption) | simp

/-- (dR and), p.132: relation preservation for this schema. -/
private theorem equation_relation_distRight_conj (A B C D : Formula P) :
    ((Term.distRight A B (.conj C D)) : Term P _ _).relation =
    ((Term.comp (Term.assocR .conj (.disj A B) C D) (Term.comp (Term.tensor .conj (Term.distRight A B C) (Term.id D)) (Term.comp (Term.distRight A (.conj B C) D) (Term.tensor .disj (Term.id A) (Term.assocL .conj B C D))))) : Term P _ _).relation := by
  funext x y
  apply propext
  rcases x with ((x | x) | (x | x)) <;>
  rcases y with (y | (y | (y | y))) <;>
  all_goals first | exact Empty.elim (by assumption) | simp

/-- (dR or), p.132: relation preservation for this schema. -/
private theorem equation_relation_distRight_disj (A B C D : Formula P) :
    ((Term.distRight (.disj A B) C D) : Term P _ _).relation =
    ((Term.comp (Term.tensor .conj (Term.assocL .disj A B C) (Term.id D)) (Term.comp (Term.distRight A (.disj B C) D) (Term.comp (Term.tensor .disj (Term.id A) (Term.distRight B C D)) (Term.assocR .disj A B (.conj C D))))) : Term P _ _).relation := by
  funext x y
  apply propext
  rcases x with (((x | x) | x) | x) <;>
  rcases y with ((y | y) | (y | y)) <;>
  all_goals first | exact Empty.elim (by assumption) | simp

/-- (d b and), p.132: relation preservation for this schema. -/
private theorem equation_relation_dist_b_conj (A B C D : Formula P) :
    ((Term.comp (Term.tensor .conj (Term.dist A B C) (Term.id D)) (Term.distRight (.conj A B) C D)) : Term P _ _).relation =
    ((Term.comp (Term.assocL .conj A (.disj B C) D) (Term.comp (Term.tensor .conj (Term.id A) (Term.distRight B C D)) (Term.dist A B (.conj C D)))) : Term P _ _).relation := by
  funext x y
  apply propext
  rcases x with ((x | (x | x)) | x) <;>
  rcases y with ((y | y) | (y | y)) <;>
  all_goals first | exact Empty.elim (by assumption) | simp

/-- (d b or), p.132: relation preservation for this schema. -/
private theorem equation_relation_dist_b_disj (A B C D : Formula P) :
    ((Term.comp (Term.dist (.disj A B) C D) (Term.tensor .disj (Term.distRight A B C) (Term.id D))) : Term P _ _).relation =
    ((Term.comp (Term.distRight A B (.disj C D)) (Term.comp (Term.tensor .disj (Term.id A) (Term.dist B C D)) (Term.assocR .disj A (.conj B C) D))) : Term P _ _).relation := by
  funext x y
  apply propext
  rcases x with ((x | x) | (x | x)) <;>
  rcases y with ((y | (y | y)) | y) <;>
  all_goals first | exact Empty.elim (by assumption) | simp

/-- (m nat), p.333: relation preservation for this schema. -/
private theorem equation_relation_mix_nat {A B D E : Formula P} (f : Term P A D) (g : Term P B E) :
    ((Term.comp (Term.mix A B) (Term.tensor .disj f g)) : Term P _ _).relation =
    ((Term.comp (Term.tensor .conj f g) (Term.mix D E)) : Term P _ _).relation := by
  funext x y
  apply propext
  rcases x with (x | x) <;>
  rcases y with (y | y) <;>
  all_goals first | exact Empty.elim (by assumption) | simp

/-- (b m), section 8.2; list p.336: relation preservation for this schema. -/
private theorem equation_relation_mix_assoc (A B C : Formula P) :
    ((Term.comp (Term.assocR .conj A B C) (Term.comp (Term.mix (.conj A B) C) (Term.tensor .disj (Term.mix A B) (Term.id C)))) : Term P _ _).relation =
    ((Term.comp (Term.tensor .conj (Term.id A) (Term.mix B C)) (Term.comp (Term.mix A (.disj B C)) (Term.assocR .disj A B C))) : Term P _ _).relation := by
  funext x y
  apply propext
  rcases x with (x | (x | x)) <;>
  rcases y with ((y | y) | y) <;>
  all_goals first | exact Empty.elim (by assumption) | simp

/-- (c m), section 8.4; list p.336: relation preservation for this schema. -/
private theorem equation_relation_mix_swap (A B : Formula P) :
    ((Term.comp (Term.swap .conj A B) (Term.mix B A)) : Term P _ _).relation =
    ((Term.comp (Term.mix A B) (Term.swap .disj A B)) : Term P _ _).relation := by
  funext x y
  apply propext
  rcases x with (x | x) <;>
  rcases y with (y | y) <;>
  all_goals first | exact Empty.elim (by assumption) | simp

/-- (w m), p.219: relation preservation for this schema. -/
private theorem equation_relation_diag_mix_codiag (A : Formula P) :
    ((Term.comp (Term.diag A) (Term.comp (Term.mix A A) (Term.codiag A))) : Term P _ _).relation =
    ((Term.id A) : Term P _ _).relation := by
  funext x y
  apply propext
  all_goals first | exact Empty.elim (by assumption) | simp

/-- (d k and), p.234: relation preservation for this schema. -/
private theorem equation_relation_dist_snd (A B C : Formula P) :
    ((Term.snd A (.disj B C)) : Term P _ _).relation =
    ((Term.comp (Term.dist A B C) (Term.tensor .disj (Term.snd A B) (Term.id C))) : Term P _ _).relation := by
  funext x y
  apply propext
  rcases x with (x | (x | x)) <;>
  rcases y with (y | y) <;>
  all_goals first | exact Empty.elim (by assumption) | simp

/-- (d k or), p.234: relation preservation for this schema. -/
private theorem equation_relation_dist_inl (A B C : Formula P) :
    ((Term.inl (.conj A B) C) : Term P _ _).relation =
    ((Term.comp (Term.tensor .conj (Term.id A) (Term.inl B C)) (Term.dist A B C)) : Term P _ _).relation := by
  funext x y
  apply propext
  rcases x with (x | x) <;>
  rcases y with ((y | y) | y) <;>
  all_goals first | exact Empty.elim (by assumption) | simp

/-- (d m), p.234: relation preservation for this schema. -/
private theorem equation_relation_dist_mix (A B C : Formula P) :
    ((Term.mix A C) : Term P _ _).relation =
    ((Term.comp (Term.tensor .conj (Term.id A) (Term.inr B C)) (Term.comp (Term.dist A B C) (Term.tensor .disj (Term.fst A B) (Term.id C)))) : Term P _ _).relation := by
  funext x y
  apply propext
  rcases x with (x | x) <;>
  rcases y with (y | y) <;>
  all_goals first | exact Empty.elim (by assumption) | simp

/-- (0I), p.288, inherited p.317: relation preservation for this schema. -/
private theorem equation_relation_zero_law {A B : Formula P} (f g : Term P A B) :
    ((Term.comp (Term.zero A) f) : Term P _ _).relation =
    ((Term.comp g (Term.zero B)) : Term P _ _).relation := by
  funext x y
  apply propext
  all_goals first | exact Empty.elim (by assumption) | simp

/-- n-r/rho isomorphism equations, pp.310,312: relation preservation for this schema. -/
private theorem equation_relation_dnOut_in (A : Formula P) :
    ((Term.comp (Term.dnOut A) (Term.dnIn A)) : Term P _ _).relation =
    ((Term.id (.neg (.neg A))) : Term P _ _).relation := by
  funext x y
  apply propext
  all_goals first | exact Empty.elim (by assumption) | simp

/-- n-r/rho isomorphism equations, pp.310,312: relation preservation for this schema. -/
private theorem equation_relation_dnOut_out (A : Formula P) :
    ((Term.comp (Term.dnIn A) (Term.dnOut A)) : Term P _ _).relation =
    ((Term.id A) : Term P _ _).relation := by
  funext x y
  apply propext
  all_goals first | exact Empty.elim (by assumption) | simp

/-- n-r/rho isomorphism equations, pp.310,312: relation preservation for this schema. -/
private theorem equation_relation_dmConjOut_in (A B : Formula P) :
    ((Term.comp (Term.dmConjOut A B) (Term.dmConjIn A B)) : Term P _ _).relation =
    ((Term.id (.neg (.conj A B))) : Term P _ _).relation := by
  funext x y
  apply propext
  rcases x with (x | x) <;>
  rcases y with (y | y) <;>
  all_goals first | exact Empty.elim (by assumption) | simp

/-- n-r/rho isomorphism equations, pp.310,312: relation preservation for this schema. -/
private theorem equation_relation_dmConjOut_out (A B : Formula P) :
    ((Term.comp (Term.dmConjIn A B) (Term.dmConjOut A B)) : Term P _ _).relation =
    ((Term.id (.disj (.neg A) (.neg B))) : Term P _ _).relation := by
  funext x y
  apply propext
  rcases x with (x | x) <;>
  rcases y with (y | y) <;>
  all_goals first | exact Empty.elim (by assumption) | simp

/-- n-r/rho isomorphism equations, pp.310,312: relation preservation for this schema. -/
private theorem equation_relation_dmDisjOut_in (A B : Formula P) :
    ((Term.comp (Term.dmDisjOut A B) (Term.dmDisjIn A B)) : Term P _ _).relation =
    ((Term.id (.neg (.disj A B))) : Term P _ _).relation := by
  funext x y
  apply propext
  rcases x with (x | x) <;>
  rcases y with (y | y) <;>
  all_goals first | exact Empty.elim (by assumption) | simp

/-- n-r/rho isomorphism equations, pp.310,312: relation preservation for this schema. -/
private theorem equation_relation_dmDisjOut_out (A B : Formula P) :
    ((Term.comp (Term.dmDisjIn A B) (Term.dmDisjOut A B)) : Term P _ _).relation =
    ((Term.id (.conj (.neg A) (.neg B))) : Term P _ _).relation := by
  funext x y
  apply propext
  rcases x with (x | x) <;>
  rcases y with (y | y) <;>
  all_goals first | exact Empty.elim (by assumption) | simp

/-- n-r/rho isomorphism equations, pp.310,312: relation preservation for this schema. -/
private theorem equation_relation_negTopOut_in  :
    ((Term.comp (Term.negTopOut) (Term.negTopIn)) : Term P _ _).relation =
    ((Term.id (.neg .top)) : Term P _ _).relation := by
  funext x y
  apply propext
  rcases x with ⟨⟩ <;>
  rcases y with ⟨⟩ <;>
  all_goals first | exact Empty.elim (by assumption) | simp

/-- n-r/rho isomorphism equations, pp.310,312: relation preservation for this schema. -/
private theorem equation_relation_negTopOut_out  :
    ((Term.comp (Term.negTopIn) (Term.negTopOut)) : Term P _ _).relation =
    ((Term.id .bot) : Term P _ _).relation := by
  funext x y
  apply propext
  rcases x with ⟨⟩ <;>
  rcases y with ⟨⟩ <;>
  all_goals first | exact Empty.elim (by assumption) | simp

/-- n-r/rho isomorphism equations, pp.310,312: relation preservation for this schema. -/
private theorem equation_relation_negBotOut_in  :
    ((Term.comp (Term.negBotOut) (Term.negBotIn)) : Term P _ _).relation =
    ((Term.id (.neg .bot)) : Term P _ _).relation := by
  funext x y
  apply propext
  rcases x with ⟨⟩ <;>
  rcases y with ⟨⟩ <;>
  all_goals first | exact Empty.elim (by assumption) | simp

/-- n-r/rho isomorphism equations, pp.310,312: relation preservation for this schema. -/
private theorem equation_relation_negBotOut_out  :
    ((Term.comp (Term.negBotIn) (Term.negBotOut)) : Term P _ _).relation =
    ((Term.id .top) : Term P _ _).relation := by
  funext x y
  apply propext
  rcases x with ⟨⟩ <;>
  rcases y with ⟨⟩ <;>
  all_goals first | exact Empty.elim (by assumption) | simp

/-- Well-definedness of all defining schemas, without a faithfulness claim. -/
theorem Equation.relation {A B : Formula P} {f g : Term P A B} (e : Equation f g) :
    f.relation = g.relation := by
  cases e with
  | @id_comp A B f =>
    exact equation_relation_id_comp _
  | @comp_id A B f =>
    exact equation_relation_comp_id _
  | @assoc A B C D f g h =>
    exact equation_relation_assoc _ _ _
  | @tensor_id o A B =>
    exact equation_relation_tensor_id _ _ _
  | @tensor_comp o A B C D E F f g h k =>
    exact equation_relation_tensor_comp _ _ _ _ _
  | @assocR_nat o A B C D E F f g h =>
    exact equation_relation_assocR_nat _ _ _ _
  | @assocL_nat o A B C D E F f g h =>
    exact equation_relation_assocL_nat _ _ _ _
  | @assocR_L o A B C =>
    exact equation_relation_assocR_L _ _ _ _
  | @assocL_R o A B C =>
    exact equation_relation_assocL_R _ _ _ _
  | @pentagon o A B C D =>
    exact equation_relation_pentagon _ _ _ _ _
  | @swap_nat o A B D E f g =>
    exact equation_relation_swap_nat _ _ _
  | @swap_swap o A B =>
    exact equation_relation_swap_swap _ _ _
  | @hexagon o A B C =>
    exact equation_relation_hexagon _ _ _ _
  | @rightOut_nat o A D f =>
    exact equation_relation_rightOut_nat _ _
  | @rightIn_nat o A D f =>
    exact equation_relation_rightIn_nat _ _
  | @rightOut_In o A =>
    exact equation_relation_rightOut_In _ _
  | @rightIn_Out o A =>
    exact equation_relation_rightIn_Out _ _
  | @leftOut_nat o A D f =>
    exact equation_relation_leftOut_nat _ _
  | @leftIn_nat o A D f =>
    exact equation_relation_leftIn_nat _ _
  | @leftOut_In o A =>
    exact equation_relation_leftOut_In _ _
  | @leftIn_Out o A =>
    exact equation_relation_leftIn_Out _ _
  | @triangle o A C =>
    exact equation_relation_triangle _ _ _
  | @diag_nat A D f =>
    exact equation_relation_diag_nat _
  | @codiag_nat A D f =>
    exact equation_relation_codiag_nat _
  | @fst_nat A B D E f g =>
    exact equation_relation_fst_nat _ _
  | @inl_nat A B D E f g =>
    exact equation_relation_inl_nat _ _
  | @snd_nat A B D E f g =>
    exact equation_relation_snd_nat _ _
  | @inr_nat A B D E f g =>
    exact equation_relation_inr_nat _ _
  | @diag_assoc A =>
    exact equation_relation_diag_assoc _
  | @codiag_assoc A =>
    exact equation_relation_codiag_assoc _
  | @diag_swap A =>
    exact equation_relation_diag_swap _
  | @codiag_swap A =>
    exact equation_relation_codiag_swap _
  | @diag_tensor A B =>
    exact equation_relation_diag_tensor _ _
  | @codiag_tensor A B =>
    exact equation_relation_codiag_tensor _ _
  | @fst_assoc A B C =>
    exact equation_relation_fst_assoc _ _ _
  | @inl_assoc A B C =>
    exact equation_relation_inl_assoc _ _ _
  | @snd_swap A B =>
    exact equation_relation_snd_swap _ _
  | @inr_swap A B =>
    exact equation_relation_inr_swap _ _
  | @diag_fst A =>
    exact equation_relation_diag_fst _
  | @inl_codiag A =>
    exact equation_relation_inl_codiag _
  | @diag_snd A =>
    exact equation_relation_diag_snd _
  | @inr_codiag A =>
    exact equation_relation_inr_codiag _
  | @fst_top A =>
    exact equation_relation_fst_top _
  | @inl_bot A =>
    exact equation_relation_inl_bot _
  | @constant_swap o C h =>
    exact equation_relation_constant_swap _ _ (by assumption)
  | @dist_nat A B C D E F f g h =>
    exact equation_relation_dist_nat _ _ _
  | @distRight_nat A B C D E F f g h =>
    exact equation_relation_distRight_nat _ _ _
  | @dist_conj A B C D =>
    exact equation_relation_dist_conj _ _ _ _
  | @dist_disj A B C D =>
    exact equation_relation_dist_disj _ _ _ _
  | @distRight_conj A B C D =>
    exact equation_relation_distRight_conj _ _ _ _
  | @distRight_disj A B C D =>
    exact equation_relation_distRight_disj _ _ _ _
  | @dist_b_conj A B C D =>
    exact equation_relation_dist_b_conj _ _ _ _
  | @dist_b_disj A B C D =>
    exact equation_relation_dist_b_disj _ _ _ _
  | @mix_nat A B D E f g =>
    exact equation_relation_mix_nat _ _
  | @mix_assoc A B C =>
    exact equation_relation_mix_assoc _ _ _
  | @mix_swap A B =>
    exact equation_relation_mix_swap _ _
  | @diag_mix_codiag A =>
    exact equation_relation_diag_mix_codiag _
  | @dist_snd A B C =>
    exact equation_relation_dist_snd _ _ _
  | @dist_inl A B C =>
    exact equation_relation_dist_inl _ _ _
  | @dist_mix A B C =>
    exact equation_relation_dist_mix _ _ _
  | @zero_law A B f g =>
    exact equation_relation_zero_law _ _
  | @dnOut_in A =>
    exact equation_relation_dnOut_in _
  | @dnOut_out A =>
    exact equation_relation_dnOut_out _
  | @dmConjOut_in A B =>
    exact equation_relation_dmConjOut_in _ _
  | @dmConjOut_out A B =>
    exact equation_relation_dmConjOut_out _ _
  | @dmDisjOut_in A B =>
    exact equation_relation_dmDisjOut_in _ _
  | @dmDisjOut_out A B =>
    exact equation_relation_dmDisjOut_out _ _
  | @negTopOut_in =>
    exact equation_relation_negTopOut_in
  | @negTopOut_out =>
    exact equation_relation_negTopOut_out
  | @negBotOut_in =>
    exact equation_relation_negBotOut_in
  | @negBotOut_out =>
    exact equation_relation_negBotOut_out

end DosenPetric.Presentation
