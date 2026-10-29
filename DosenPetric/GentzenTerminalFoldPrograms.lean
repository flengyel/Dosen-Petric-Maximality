module

public import DosenPetric.GentzenTerminalDisjDenotation
public import DosenPetric.GentzenInverseContextAssociativity

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.TerminalFold
universe u
variable {P : Type u}

theorem parallel_out {K F : List (NormalForm P)} (p : Route K F) (A : NormalForm P) :
    comp (ofTerm (p.parallel (Route.identity [A])).product) (out F A) =
      comp (out K A) (tensor .conj (ofTerm p.product) (id A)) := by
  have he := Route.parallel_split .conj p (Route.identity [A])
  rw [Route.identity_arrow] at he
  dsimp only [side,sideM,conjMonoidal,category,split] at he
  simp only [out,Laws.assoc]
  rw [← Laws.assoc (ofTerm (p.parallel (Route.identity [A])).product)]
  erw [he]
  simp only [Laws.assoc,Laws.tensor_comp,Laws.id_comp,Laws.comp_id]
  rfl

/-- Associating the two fixed blocks commutes with removing the terminal unit. -/
theorem out_assoc (T F : List (NormalForm P)) (A : NormalForm P) :
    comp ((ExchangeScript.appendAssoc T F [A]).arrow .conj)
      (comp (out (T++F) A) (tensor .conj (ofTerm (append .conj T F).invTerm) (id A))) =
      comp (ofTerm (append .conj T (F++[A])).invTerm)
        (comp (tensor .conj (id (ante T)) (out F A)) (assocR .conj (ante T) (ante F) A)) := by
  have he := congrArg (fun v => comp v (tensor .conj (id (.conj (ante T) (ante F))) (rightOut .conj A)))
    (split_assoc .conj T F [A])
  dsimp only [side,sideM,conjMonoidal,category,split] at he
  have hn : comp (assocR .conj (ante T) (ante F) (.conj A .top))
      (tensor .conj (id (.conj (ante T) (ante F))) (rightOut .conj A)) =
      comp (tensor .conj (id (ante T)) (tensor .conj (id (ante F)) (rightOut .conj A)))
        (assocR .conj (ante T) (ante F) A) := by
    simpa only [Laws.tensor_id] using
      Laws.assocR_nat .conj (id (ante T)) (id (ante F)) (rightOut .conj A)
  simp only [Laws.assoc] at he
  rw [hn] at he
  simp only [out,tensor_factor,Laws.assoc]
  simp only [Laws.tensor_comp,Laws.id_comp,Laws.comp_id] at he ⊢
  exact he

/-- Reverse association in the child's fixed input, with its selected terminal
    formula kept outside the fixed block. -/
theorem inverse_out_assoc (T F : List (NormalForm P)) (A : NormalForm P) :
    comp ((ExchangeScript.appendAssoc T F [A]).inverse.arrow .conj)
      (comp (ofTerm (append .conj T (F++[A])).invTerm)
        (tensor .conj (id (ante T)) (out F A))) =
      comp (out (T++F) A)
        (comp (tensor .conj (ofTerm (append .conj T F).invTerm) (id A))
          (assocL .conj (ante T) (ante F) A)) := by
  let a := ExchangeScript.appendAssoc T F [A]
  apply cancel_left _ _ (a.arrow .conj) (a.inverse.arrow .conj) (a.inverse_arrow .conj)
  rw [← Laws.assoc]
  have ha := a.arrow_inverse .conj
  dsimp only [side,category] at ha
  erw [ha]
  rw [Laws.id_comp]
  have he := congrArg (fun v => comp v (assocL .conj (ante T) (ante F) A)) (out_assoc T F A)
  simpa only [a,Laws.assoc,Laws.assocR_L,Laws.comp_id] using he.symm

/-- Decode the child cut at its terminal component. -/
theorem child_into (T F : List (NormalForm P)) (A : NormalForm P) :
    comp (tensor .conj (ofTerm (append .conj T F).toTerm) (id A))
      (comp (into (T++F) A)
        (comp ((ExchangeScript.appendAssoc T F [A]).inverse.arrow .conj)
          (ofTerm (append .conj T (F++[A])).invTerm))) =
      comp (assocL .conj (ante T) (ante F) A)
        (tensor .conj (id (ante T)) (into F A)) := by
  have hi : comp (tensor .conj (id (ante T)) (out F A))
      (tensor .conj (id (ante T)) (into F A)) = id (.conj (ante T) (ante (F++[A]))) := by
    rw [Laws.tensor_comp,Laws.id_comp,out_into,Laws.tensor_id]
  apply cancel_right _ _ (tensor .conj (id (ante T)) (out F A))
    (tensor .conj (id (ante T)) (into F A)) hi
  simp only [Laws.assoc]
  rw [inverse_out_assoc]
  rw [← Laws.assoc (into (T++F) A),into_out]
  rw [Laws.id_comp,← Laws.assoc (tensor .conj (ofTerm (append .conj T F).toTerm) (id A)),
    Laws.tensor_comp,(append .conj T F).to_inv,Laws.id_comp,Laws.tensor_id,Laws.id_comp]
  rw [Laws.tensor_comp,Laws.id_comp,into_out,Laws.tensor_id,Laws.comp_id]

end DosenPetric.Reduced.Gentzen.TerminalFold
