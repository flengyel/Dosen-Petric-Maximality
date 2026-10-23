module

public import DosenPetric.ReducedUnionOccurrences
public import DosenPetric.AtomicPorts

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

@[reducible] def fold (o : Op) : List (NormalForm P) → NormalForm P
  | [] => o.unit
  | A :: Γ => o.formula A (fold o Γ)

theorem fold_as_foldr (o : Op) (Γ : List (NormalForm P)) :
    fold o Γ = Γ.foldr o.formula o.unit := by
  induction Γ with
  | nil => rfl
  | cons A Γ ih => exact congrArg (o.formula A) ih
abbrev ante (Γ : List (NormalForm P)) := fold .conj Γ
abbrev succ (Δ : List (NormalForm P)) := fold .disj Δ

/-- Explicit positive comparison in the existing syntactic quotient. -/
structure Iso (A B : NormalForm P) where
  toTerm : Term P A B
  invTerm : Term P B A
  positive_to : toTerm.Positive
  positive_inv : invTerm.Positive
  to_inv : comp (ofTerm toTerm) (ofTerm invTerm) = id A
  inv_to : comp (ofTerm invTerm) (ofTerm toTerm) = id B

namespace Iso

def refl (A : NormalForm P) : Iso A A where
  toTerm := .id A
  invTerm := .id A
  positive_to := .id A
  positive_inv := .id A
  to_inv := Laws.id_comp _
  inv_to := Laws.id_comp _

def symm {A B : NormalForm P} (i : Iso A B) : Iso B A where
  toTerm := i.invTerm
  invTerm := i.toTerm
  positive_to := i.positive_inv
  positive_inv := i.positive_to
  to_inv := i.inv_to
  inv_to := i.to_inv

def trans {A B C : NormalForm P} (i : Iso A B) (j : Iso B C) : Iso A C where
  toTerm := .comp i.toTerm j.toTerm
  invTerm := .comp j.invTerm i.invTerm
  positive_to := .comp i.positive_to j.positive_to
  positive_inv := .comp j.positive_inv i.positive_inv
  to_inv := by
    change comp (comp (ofTerm i.toTerm) (ofTerm j.toTerm))
      (comp (ofTerm j.invTerm) (ofTerm i.invTerm)) = _
    rw [Laws.assoc, ← Laws.assoc (ofTerm j.toTerm), j.to_inv, Laws.id_comp, i.to_inv]
  inv_to := by
    change comp (comp (ofTerm j.invTerm) (ofTerm i.invTerm))
      (comp (ofTerm i.toTerm) (ofTerm j.toTerm)) = _
    rw [Laws.assoc, ← Laws.assoc (ofTerm i.invTerm), i.inv_to, Laws.id_comp, j.inv_to]

def tensor (o : Op) {A B C D : NormalForm P} (i : Iso A B) (j : Iso C D) :
    Iso (o.formula A C) (o.formula B D) where
  toTerm := .tensor o i.toTerm j.toTerm
  invTerm := .tensor o i.invTerm j.invTerm
  positive_to := .tensor o i.positive_to j.positive_to
  positive_inv := .tensor o i.positive_inv j.positive_inv
  to_inv := by
    change comp (Reduced.tensor o (ofTerm i.toTerm) (ofTerm j.toTerm))
      (Reduced.tensor o (ofTerm i.invTerm) (ofTerm j.invTerm)) = _
    rw [Laws.tensor_comp, i.to_inv, j.to_inv, Laws.tensor_id]
  inv_to := by
    change comp (Reduced.tensor o (ofTerm i.invTerm) (ofTerm j.invTerm))
      (Reduced.tensor o (ofTerm i.toTerm) (ofTerm j.toTerm)) = _
    rw [Laws.tensor_comp, i.inv_to, j.inv_to, Laws.tensor_id]

def assoc (o : Op) (A B C : NormalForm P) :
    Iso (o.formula (o.formula A B) C) (o.formula A (o.formula B C)) where
  toTerm := .assocL o A B C
  invTerm := .assocR o A B C
  positive_to := .assocL ..
  positive_inv := .assocR ..
  to_inv := Laws.assocL_R ..
  inv_to := Laws.assocR_L ..

def swap (o : Op) (A B : NormalForm P) : Iso (o.formula A B) (o.formula B A) where
  toTerm := .swap o A B
  invTerm := .swap o B A
  positive_to := .swap ..
  positive_inv := .swap ..
  to_inv := Laws.swap_swap ..
  inv_to := Laws.swap_swap ..

def leftUnit (o : Op) (A : NormalForm P) : Iso (o.formula o.unit A) A where
  toTerm := .leftOut o A
  invTerm := .leftIn o A
  positive_to := .leftOut ..
  positive_inv := .leftIn ..
  to_inv := Laws.leftOut_In ..
  inv_to := Laws.leftIn_Out ..

def rightUnit (o : Op) (A : NormalForm P) : Iso (o.formula A o.unit) A where
  toTerm := .rightOut o A
  invTerm := .rightIn o A
  positive_to := .rightOut ..
  positive_inv := .rightIn ..
  to_inv := Laws.rightOut_In ..
  inv_to := Laws.rightIn_Out ..

end Iso

/-- Fold concatenation is compared by actual unit and associativity arrows. -/
def append (o : Op) : (Γ Δ : List (NormalForm P)) →
    Iso (o.formula (fold o Γ) (fold o Δ)) (fold o (Γ ++ Δ))
  | [], Δ => Iso.leftUnit o (fold o Δ)
  | A :: Γ, Δ => (Iso.assoc o A (fold o Γ) (fold o Δ)).trans
      (Iso.tensor o (Iso.refl A) (append o Γ Δ))

/-- Lift a comparison through a fixed prefix; this changes selected positions only. -/
def under (o : Op) (Γ : List (NormalForm P)) {A B : NormalForm P} (i : Iso A B) :
    Iso (Γ.foldr o.formula A) (Γ.foldr o.formula B) :=
  match Γ with
  | [] => i
  | C :: Γ => Iso.tensor o (Iso.refl C) (under o Γ i)

/-- Block exchange with four explicit positional subcontexts. -/
def exchange (o : Op) (Γ X Y Δ : List (NormalForm P)) :
    Iso (fold o (Γ ++ X ++ Y ++ Δ)) (fold o (Γ ++ Y ++ X ++ Δ)) := by
  let middle : Iso (fold o (X ++ Y ++ Δ)) (fold o (Y ++ X ++ Δ)) :=
    ((append o (X ++ Y) Δ).symm).trans
      ((Iso.tensor o ((append o X Y).symm.trans
        ((Iso.swap o (fold o X) (fold o Y)).trans (append o Y X)))
          (Iso.refl (fold o Δ))).trans (append o (Y ++ X) Δ))
  simpa only [List.append_assoc, fold_as_foldr, List.foldr_append] using under o Γ middle

/-- Singleton encoding and decoding. -/
def encode {A B : NormalForm P} (t : Term P A B) : Term P (ante [A]) (succ [B]) :=
  .comp (.rightOut .conj A) (.comp t (.rightIn .disj B))

def decode {A B : NormalForm P} (g : Term P (ante [A]) (succ [B])) : Hom A B :=
  comp (rightIn .conj A) (comp (ofTerm g) (rightOut .disj B))

theorem decode_encode {A B : NormalForm P} (t : Term P A B) : decode (encode t) = ofTerm t := by
  change comp (rightIn .conj A)
    (comp (comp (rightOut .conj A) (comp (ofTerm t) (rightIn .disj B))) (rightOut .disj B)) = _
  simp only [Laws.assoc]
  rw [← Laws.assoc (rightIn .conj A), Laws.rightIn_Out, Laws.id_comp,
    Laws.rightIn_Out, Laws.comp_id]

end DosenPetric.Reduced.Gentzen
