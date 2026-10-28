module

public import DosenPetric.GentzenExchangeScripts
public import DosenPetric.GentzenTraceCompatibility

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

namespace At

/-- Delete precisely this tagged position, preserving the order of all others. -/
def erase {Γ : List (NormalForm P)} {C : NormalForm P} : At Γ C → List (NormalForm P)
  | .here _ Γ => Γ
  | @there _ _ B _ a => B :: a.erase

def preceding {Γ : List (NormalForm P)} {C : NormalForm P} : At Γ C → List (NormalForm P)
  | .here _ _ => []
  | @there _ _ B _ a => B :: a.preceding

def suffix {Γ : List (NormalForm P)} {C : NormalForm P} : At Γ C → List (NormalForm P)
  | .here _ Γ => Γ
  | .there a => a.suffix

theorem context_eq {Γ : List (NormalForm P)} {C : NormalForm P} (a : At Γ C) :
    a.preceding ++ C :: a.suffix = Γ := by
  induction a with
  | here => rfl
  | there a ih => exact congrArg (fun xs => _ :: xs) ih

theorem erase_eq {Γ : List (NormalForm P)} {C : NormalForm P} (a : At Γ C) :
    a.preceding ++ a.suffix = a.erase := by
  induction a with
  | here => rfl
  | there a ih => exact congrArg (fun xs => _ :: xs) ih

theorem preceding_length {Γ : List (NormalForm P)} {C : NormalForm P} (a : At Γ C) :
    a.preceding.length = a.index := by
  induction a with
  | here => rfl
  | there a ih => exact congrArg Nat.succ ih

/-- Include the surviving tags into the original list. -/
def retain {Γ : List (NormalForm P)} {C : NormalForm P} (a : At Γ C)
    {B : NormalForm P} : At a.erase B → At Γ B :=
  match a with
  | .here _ _ => At.there
  | .there a => fun b => match b with
    | .here _ _ => .here _ _
    | .there b => .there (a.retain b)

theorem retain_index {Γ : List (NormalForm P)} {C B : NormalForm P}
    (a : At Γ C) (b : At a.erase B) :
    (a.retain b).index = if b.index < a.index then b.index else b.index + 1 := by
  induction a with
  | here => simp only [retain, index, Nat.not_lt_zero, ite_false]
  | there a ih => cases b with
    | here => simp only [retain, index, Nat.zero_lt_succ, ite_true]
    | there b =>
      simp only [retain, index, ih]
      by_cases h : b.index < a.index
      · rw [ite_eq_left h, ite_eq_left (by omega)]
      · rw [ite_eq_right h, ite_eq_right (by omega)]

/-- Move the selected position to the head; a head selection is the identity script. -/
def toHead {Γ : List (NormalForm P)} {C : NormalForm P} (a : At Γ C) :
    ExchangeScript P (C :: a.erase) Γ := by
  cases a with
  | here C Γ => exact .identity (C :: Γ)
  | @there C B Γ a =>
    exact (ExchangeScript.exchange [] (B :: a.preceding) [C] a.suffix).reindex
      (by simp only [List.nil_append, List.cons_append];
          rw [erase_eq]; rfl)
      (by simpa only [List.nil_append, List.append_assoc, List.singleton_append,
          List.cons_append] using congrArg (fun xs => B :: xs) a.context_eq)

theorem toHead_get {Γ : List (NormalForm P)} {C : NormalForm P} (a : At Γ C) :
    a.toHead.get a = .here C a.erase := by
  cases a with
  | here => rfl
  | there a =>
    apply At.index_injective
    simp only [toHead, ExchangeScript.get, ExchangeScript.rewire,
      Rewire.get, index_cast, swapBlocks_index, preceding_length, List.length_nil,
      List.length_cons, index]
    simp only [exchangeIndex, Nat.zero_add]
    split <;> (try split) <;> (try split) <;> omega

theorem toHead_get_index {Γ : List (NormalForm P)} {C B : NormalForm P}
    (a : At Γ C) (b : At Γ B) :
    (a.toHead.get b).index = exchangeIndex 0 a.index 1 b.index := by
  cases a with
  | here =>
    change b.index = exchangeIndex 0 0 1 b.index
    simp only [exchangeIndex, Nat.not_lt_zero, ite_false, Nat.zero_add, Nat.sub_zero]
    split <;> rfl
  | there a =>
    simp only [toHead, ExchangeScript.get, ExchangeScript.rewire, Rewire.get,
      index_cast, swapBlocks_index, List.length_nil, List.length_cons, preceding_length, index, Nat.zero_add]

theorem toHead_get_retain {Γ : List (NormalForm P)} {C B : NormalForm P}
    (a : At Γ C) (b : At a.erase B) : a.toHead.get (a.retain b) = .there b := by
  apply index_injective
  rw [toHead_get_index, retain_index]
  change exchangeIndex 0 a.index 1 (if b.index < a.index then b.index else b.index + 1) = b.index + 1
  unfold exchangeIndex
  by_cases h : b.index < a.index
  · rw [ite_eq_left h]
    split <;> (try split) <;> (try split) <;> omega
  · rw [ite_eq_right h]
    split <;> (try split) <;> (try split) <;> omega

theorem erase_shift (Γ Θ : List (NormalForm P)) (C : NormalForm P) :
    (At.shift Γ (.here C Θ)).erase = Γ ++ Θ := by
  induction Γ with
  | nil => rfl
  | cons B Γ ih => exact congrArg (fun xs => B :: xs) ih

end At
end DosenPetric.Reduced.Gentzen
