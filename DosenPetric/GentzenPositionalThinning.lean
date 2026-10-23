module

public import DosenPetric.GentzenHeadAtomization

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

theorem thin_index (Γ Θ : List (NormalForm P)) (A : NormalForm P)
    {B : NormalForm P} (a : At (Γ ++ Θ) B) :
    ((Route.thin Γ Θ A).get a).index = if a.index < Γ.length then a.index else a.index + 1 := by
  induction Γ with
  | nil =>
    simp only [Route.thin, Route.get_map, Route.get_identity, At.index, List.length_nil,
      Nat.not_lt_zero, ite_false]
  | cons C Γ ih =>
    cases a with
    | here =>
      change 0 = if 0 < Γ.length + 1 then 0 else 1
      have hp : 0 < Γ.length + 1 := by omega
      rw [ite_eq_left hp]
    | there a =>
      change ((Route.map At.there (Route.thin Γ Θ A)).get a).index =
        if a.index + 1 < Γ.length + 1 then a.index + 1 else a.index + 1 + 1
      rw [Route.get_map]
      change ((Route.thin Γ Θ A).get a).index + 1 = _
      rw [ih a]
      split <;> (try split) <;> omega

namespace Rewire

def moveHead (Γ Θ : List (NormalForm P)) (A : NormalForm P) :
    Rewire P (Γ ++ A :: Θ) (A :: (Γ ++ Θ)) :=
  (Rewire.exchange [] [A] Γ Θ).reindex
    (by simp only [List.nil_append, List.append_assoc, List.singleton_append])
    (by simp only [List.nil_append, List.cons_append])

theorem moveHead_index (Γ Θ : List (NormalForm P)) (A : NormalForm P)
    {B : NormalForm P} (a : At (A :: (Γ ++ Θ)) B) :
    ((moveHead Γ Θ A).get a).index = exchangeIndex 0 1 Γ.length a.index := by
  simp only [moveHead, get, swapBlocks_index, At.index_cast,
    List.length_nil, List.length_cons]

theorem moveHead_thin (o : Op) (Γ Θ : List (NormalForm P)) (A : NormalForm P) :
    (side P o).comp ((moveHead Γ Θ A).arrow o) ((Route.thin [] (Γ ++ Θ) A).sideArrow o) =
      (Route.thin Γ Θ A).sideArrow o := by
  let C := side P o
  apply side_ext o
  intro B a
  rw [C.assoc, Route.sideArrow_get, arrow_component, Route.sideArrow_get]
  apply congrArg (component o)
  apply At.index_injective
  rw [moveHead_index, thin_index, thin_index]
  simp only [List.length_nil, Nat.not_lt_zero, ite_false, exchangeIndex, Nat.zero_add]
  split <;> (try split) <;> (try split) <;> omega

theorem moveHead_snd (o : Op) (Γ Θ : List (NormalForm P)) (A : NormalForm P) :
    (side P o).comp ((moveHead Γ Θ A).arrow o) ((sideD P o).snd A (fold o (Γ ++ Θ))) =
      (Route.thin Γ Θ A).sideArrow o := by
  rw [← thin_head]
  exact moveHead_thin o Γ Θ A
end Rewire

namespace G

def atomThinL (Γ Θ Δ : List (NormalForm P)) (A : NormalForm P) (f : G P (Γ ++ Θ) Δ) :
    G P (Γ ++ A :: Θ) Δ := (Rewire.moveHead Γ Θ A).left (headThinL A f)

def atomThinR (Γ Δ Λ : List (NormalForm P)) (A : NormalForm P) (f : G P Γ (Δ ++ Λ)) :
    G P Γ (Δ ++ A :: Λ) := (Rewire.moveHead Δ Λ A).right (headThinR A f)

theorem atomThinL_atomized (Γ Θ Δ : List (NormalForm P)) (A : NormalForm P)
    (f : G P (Γ ++ Θ) Δ) (hf : f.Atomized) : (atomThinL Γ Θ Δ A f).Atomized :=
  (Rewire.left_atomized _ _).mpr (headThinL_atomized A f hf)

theorem atomThinR_atomized (Γ Δ Λ : List (NormalForm P)) (A : NormalForm P)
    (f : G P Γ (Δ ++ Λ)) (hf : f.Atomized) : (atomThinR Γ Δ Λ A f).Atomized :=
  (Rewire.right_atomized _ _).mpr (headThinR_atomized A f hf)

theorem atomThinL_cutFree (Γ Θ Δ : List (NormalForm P)) (A : NormalForm P)
    (f : G P (Γ ++ Θ) Δ) (hf : f.CutFree) : (atomThinL Γ Θ Δ A f).CutFree := by
  change ((Rewire.moveHead Γ Θ A).left (headThinL A f)).cutCount = 0
  rw [Rewire.left_count]
  exact headThinL_cutFree A f hf

theorem atomThinR_cutFree (Γ Δ Λ : List (NormalForm P)) (A : NormalForm P)
    (f : G P Γ (Δ ++ Λ)) (hf : f.CutFree) : (atomThinR Γ Δ Λ A f).CutFree := by
  change ((Rewire.moveHead Δ Λ A).right (headThinR A f)).cutCount = 0
  rw [Rewire.right_count]
  exact headThinR_cutFree A f hf

theorem atomThinL_denote (Γ Θ Δ : List (NormalForm P)) (A : NormalForm P)
    (f : G P (Γ ++ Θ) Δ) :
    ofTerm (atomThinL Γ Θ Δ A f).denote = ofTerm (G.thinL Γ Θ Δ A f).denote := by
  rw [atomThinL, Rewire.left_denote, headThinL_denote]
  have hm : comp ((Rewire.moveHead Γ Θ A).arrow .conj) (snd A (ante (Γ ++ Θ))) =
      ofTerm (Route.thin Γ Θ A).product := Rewire.moveHead_snd .conj Γ Θ A
  exact (Laws.assoc ..).symm.trans (congrArg (fun k => comp k (ofTerm f.denote)) hm)

theorem atomThinR_denote (Γ Δ Λ : List (NormalForm P)) (A : NormalForm P)
    (f : G P Γ (Δ ++ Λ)) :
    ofTerm (atomThinR Γ Δ Λ A f).denote = ofTerm (G.thinR Γ Δ Λ A f).denote := by
  rw [atomThinR, Rewire.right_denote, headThinR_denote]
  have hm : comp (inr A (succ (Δ ++ Λ))) ((Rewire.moveHead Δ Λ A).arrow .disj) =
      ofTerm (Route.thin Δ Λ A).coproduct := Rewire.moveHead_snd .disj Δ Λ A
  exact (Laws.assoc ..).trans (congrArg (fun k => comp (ofTerm f.denote) k) hm)

end G
end DosenPetric.Reduced.Gentzen
