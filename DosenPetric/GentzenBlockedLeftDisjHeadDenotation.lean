module

public import DosenPetric.GentzenBlockedLeftDisjNative

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.BlockedLeftDisj
universe u
variable {P : Type u}

theorem headParent_decoded {Y F H D E : List (NormalForm P)} {A B C : NormalForm P}
    (p : Route Y F) (q : Route Y H)
    (f : G P (C::(F++[A])) D) (g : G P (C::(H++[B])) E) :
    comp (TerminalFold.into (C::Y) (.disj A B)) (ofTerm (headParent p q f g).denote) =
      comp (assocL .conj C (ante Y) (.disj A B))
        (comp (sharedParent (p.sideArrow .conj) (q.sideArrow .conj) (childArrow f) (childArrow g))
          (ofTerm (append .disj D E).toTerm)) := by
  have hr := Route.append_split .conj (p.head C) (q.head C)
  rw [Route.head_side,Route.head_side] at hr
  dsimp only [side,sideD,sideM,conjMonoidal,category,split,conjDiagonal,DiagonalData.pair] at hr
  rw [headParent,StructuralProgram.left_denote,Route.program_arrow,TerminalFold.disjLLast_denote]
  unfold TerminalFold.sourceInput
  simp only [Laws.assoc]
  erw [← Laws.assoc (ofTerm ((((p.head C).append (q.head C)).parallel
      (Route.identity [.disj A B])).product)),TerminalFold.parallel_out]
  simp only [Laws.assoc]
  rw [← Laws.assoc (TerminalFold.into (C::Y) (.disj A B)),TerminalFold.into_out,Laws.id_comp,
    ← Laws.assoc (tensor .conj (ofTerm ((p.head C).append (q.head C)).product) (id (.disj A B))),
    Laws.tensor_comp,Laws.id_comp]
  erw [hr]
  rw [sharedParent_fan]
  simp only [Laws.assoc]
  rw [← Laws.assoc (assocL .conj C (ante Y) (.disj A B)),Laws.assocL_R,Laws.id_comp]
  rw [TerminalFold.into_cons,TerminalFold.into_cons]
  simp only [childArrow,Laws.assoc]
  rfl

theorem headParent_denote {Y F H D E : List (NormalForm P)} {A B C : NormalForm P}
    (p : Route Y F) (q : Route Y H)
    (f : G P (C::(F++[A])) D) (g : G P (C::(H++[B])) E) :
    ofTerm (headParent p q f g).denote =
      comp (tensor .conj (id C) (TerminalFold.out Y (.disj A B)))
        (comp (sharedParent (p.sideArrow .conj) (q.sideArrow .conj) (childArrow f) (childArrow g))
          (ofTerm (append .disj D E).toTerm)) := by
  apply cancel_left _ _ (TerminalFold.into (C::Y) (.disj A B))
    (TerminalFold.out (C::Y) (.disj A B)) (TerminalFold.out_into (C::Y) (.disj A B))
  rw [headParent_decoded,TerminalFold.into_cons]
  simp only [Laws.assoc]
  rw [← Laws.assoc (tensor .conj (id C) (TerminalFold.into Y (.disj A B))),
    Laws.tensor_comp,Laws.id_comp,TerminalFold.into_out,Laws.tensor_id,Laws.id_comp]

end DosenPetric.Reduced.Gentzen.BlockedLeftDisj
