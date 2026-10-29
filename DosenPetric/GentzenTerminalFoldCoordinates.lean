module

public import DosenPetric.GentzenBlockedGammaConj
public import DosenPetric.GentzenRotationInverses

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.TerminalFold
universe u
variable {P : Type u}

/-- Remove the singleton fold's terminal unit. -/
def out (F : List (NormalForm P)) (A : NormalForm P) :
    Hom (ante (F++[A])) (.conj (ante F) A) :=
  comp (ofTerm (append .conj F [A]).invTerm) (tensor .conj (id (ante F)) (rightOut .conj A))

/-- Restore the singleton fold's terminal unit. -/
def into (F : List (NormalForm P)) (A : NormalForm P) :
    Hom (.conj (ante F) A) (ante (F++[A])) :=
  comp (tensor .conj (id (ante F)) (rightIn .conj A)) (ofTerm (append .conj F [A]).toTerm)

theorem out_into (F : List (NormalForm P)) (A : NormalForm P) :
    comp (out F A) (into F A) = id (ante (F++[A])) := by
  simp only [out,into,Laws.assoc]
  rw [← Laws.assoc (tensor .conj (id (ante F)) (rightOut .conj A)),
    Laws.tensor_comp,Laws.id_comp,Laws.rightOut_In,Laws.tensor_id,Laws.id_comp]
  exact (append .conj F [A]).inv_to

theorem into_out (F : List (NormalForm P)) (A : NormalForm P) :
    comp (into F A) (out F A) = id (.conj (ante F) A) := by
  simp only [out,into,Laws.assoc]
  rw [← Laws.assoc (ofTerm (append .conj F [A]).toTerm),
    (append .conj F [A]).to_inv,Laws.id_comp,Laws.tensor_comp,
    Laws.id_comp,Laws.rightIn_Out,Laws.tensor_id]

/-- The actual terminal rotation, including its empty-context instance. -/
theorem join_toTail (F : List (NormalForm P)) (A : NormalForm P) :
    comp (ofTerm (append .conj F [A]).toTerm) (ofTerm (Route.toTail F A).product) =
      comp (tensor .conj (id (ante F)) (rightOut .conj A)) (swap .conj (ante F) A) := by
  apply Reduced.conj_ext
  · rw [Laws.assoc]
    change comp (ofTerm (append .conj F [A]).toTerm)
      (comp (ofTerm (Route.toTail F A).product) (ofTerm (At.here A F).projection)) = _
    rw [Route.product_get,Route.toTail_here]
    have he := join_shift .conj F (At.here A [])
    dsimp only [side,sideD,sideM,conjMonoidal,category,join,component] at he
    rw [he]
    rw [Laws.assoc,← Laws.snd_swap,← Laws.snd_nat]
    change comp (snd (ante F) (.conj A .top)) (fst A .top) =
      comp (snd (ante F) (.conj A .top)) (rightOut .conj A)
    rw [Laws.fst_top]
  · apply product_positions
    intro B a
    rw [Laws.assoc]
    change comp (comp (ofTerm (append .conj F [A]).toTerm) (ofTerm (Route.toTail F A).product))
      (ofTerm (At.there (B := A) a).projection) = _
    rw [Laws.assoc,Route.product_get,Route.toTail_there]
    have he := join_before .conj a [A]
    dsimp only [side,sideD,sideM,conjMonoidal,category,join,component] at he
    rw [he]
    simp only [Laws.assoc]
    rw [← Laws.assoc (swap .conj (ante F) A),swap_snd,
      ← Laws.assoc (tensor .conj (id (ante F)) (rightOut .conj A)),← Laws.fst_nat,Laws.comp_id]
    rfl

theorem toTail_eq (F : List (NormalForm P)) (A : NormalForm P) :
    ofTerm (Route.toTail F A).product = comp (out F A) (swap .conj (ante F) A) := by
  apply cancel_left _ _ (ofTerm (append .conj F [A]).toTerm)
    (ofTerm (append .conj F [A]).invTerm) ((append .conj F [A]).inv_to)
  rw [join_toTail]
  simp only [out,← Laws.assoc]
  rw [(append .conj F [A]).to_inv,Laws.id_comp]

theorem toHead_eq (F : List (NormalForm P)) (A : NormalForm P) :
    ofTerm (Route.toHead F A).product = comp (swap .conj A (ante F)) (into F A) := by
  have hh : comp (ofTerm (Route.toHead F A).product) (ofTerm (Route.toTail F A).product) =
      id (ante (A::F)) := Route.rotations_head .conj F A
  have ht : comp (ofTerm (Route.toTail F A).product) (ofTerm (Route.toHead F A).product) =
      id (ante (F++[A])) := Route.rotations_tail .conj F A
  apply cancel_left _ _ (ofTerm (Route.toTail F A).product) (ofTerm (Route.toHead F A).product) hh
  rw [ht,toTail_eq,Laws.assoc,← Laws.assoc (swap .conj (ante F) A),Laws.swap_swap,
    Laws.id_comp,out_into]

end DosenPetric.Reduced.Gentzen.TerminalFold
