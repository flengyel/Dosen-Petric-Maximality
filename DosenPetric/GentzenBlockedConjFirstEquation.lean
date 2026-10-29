module

public import DosenPetric.GentzenBlockedConjFirstData
public import DosenPetric.GentzenSequentialRightSourceTransport

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace SequentialConjFirst

def routed {K Γ Θ F U I J : List (NormalForm P)} (C : NormalForm P) (p : Route K (F++U))
    (l : G P (I++((I++Γ)++Θ)) (J++((J++F)++U))) : G P (I++(Γ++Θ)) (J++K) :=
  (((p.head C).program.residual _ _ (p.head_singleFiber C)).prefixFixed J).right (rebuild C l)

theorem routed_count {K Γ Θ F U I J : List (NormalForm P)} (C : NormalForm P) (p : Route K (F++U))
    (l : G P (I++((I++Γ)++Θ)) (J++((J++F)++U))) : (routed C p l).cutCount = l.cutCount := by
  rw [routed,StructuralProgram.right_count,rebuild_count]

theorem routed_congr {K Γ Θ F U I J : List (NormalForm P)} (C : NormalForm P) (p : Route K (F++U))
    (l l' : G P (I++((I++Γ)++Θ)) (J++((J++F)++U))) (he : ofTerm l.denote = ofTerm l'.denote) :
    ofTerm (routed C p l).denote = ofTerm (routed C p l').denote := by
  rw [routed,routed,StructuralProgram.right_denote,StructuralProgram.right_denote,rebuild_congr _ _ _ he]

theorem routed_equation {K Γ Θ F U I J : List (NormalForm P)} {A B : NormalForm P}
    (p : Route K (F++U)) (f : G P Γ (A::.conj A B::F)) (g : G P Θ (B::U))
    (h : G P I J) (z : At I (.conj A B)) :
    ofTerm (PositionalCut.cut ((p.head (.conj A B)).program.right (parent f g))
      (.here (.conj A B) K) h z).denote =
      ofTerm (routed (.conj A B) p
        (G.cut (fresh (G.cut (child f) (z.toHead.left h)) g) (z.toHead.left h))).denote := by
  apply (CutCommutation.same_right (p.head (.conj A B)).program _ _ (p.head_singleFiber (.conj A B))
    (parent f g) h z).trans
  rw [routed,StructuralProgram.right_denote,StructuralProgram.right_denote]
  exact congrArg (fun k => comp k _) (native_equation f g (z.toHead.left h))

end SequentialConjFirst
namespace BlockedConjFirst

theorem selected_parent {A B : NormalForm P} {Γ Θ X Y U : List (NormalForm P)}
    (f : G P Γ (A::(X++.conj A B::Y))) (g : G P Θ (B::U)) :
    ofTerm ((block A B X Y U).keep.toHead.right (parent f g)).denote =
      ofTerm (((residue A B X Y U).head (.conj A B)).program.right
        (SequentialConjFirst.parent (SequentialConjFirst.firstChild (parametric A B X Y) f) g)).denote := by
  have he := SequentialRepair.front_source_denote (block A B X Y U).route (block A B X Y U).keep
    ((parametric A B X Y).before U) (rawResidue A B X Y U)
    (fresh_get A B X Y U) (parametric_get A B X Y U) (fun v => rawResidue_retained A B X Y U v)
    (G.conjR (Δ:=X++.conj A B::Y) (Λ:=U) f g)
  rw [ExchangeScript.right_denote,parent,ContractionBlock.denoteR]
  apply he.trans
  let old := (LogicalDeletion.headUnder [] [.conj A B] ((parametric A B X Y).before U)).right
    (G.conjR (Δ:=X++.conj A B::Y) (Λ:=U) f g)
  let canonical := SequentialConjFirst.body (SequentialConjFirst.firstChild (parametric A B X Y) f) g
  have hctx : .conj A B::.conj A B::((parametric A B X Y).before U).erase =
      .conj A B::.conj A B::((parametric A B X Y).erase++U) :=
    congrArg (fun xs => (.conj A B : NormalForm P)::.conj A B::xs) ((parametric A B X Y).erase_before U)
  have hb0 : ofTerm (old.reindex rfl hctx).denote = ofTerm canonical.denote :=
    SequentialConjFirst.selected_body (parametric A B X Y) f g
  have hb := G.reindex_right_cancel_denote hctx old canonical hb0
  have hc := SequentialRepair.headParentRight_congr _ _ hb
  have ht := congrArg (fun k => comp k (((rawResidue A B X Y U).head (.conj A B)).program.arrow .disj)) hc
  rw [StructuralProgram.right_denote]
  apply ht.trans
  rw [← StructuralProgram.right_denote,
    SequentialRepair.headParentRight_reindex ((parametric A B X Y).erase_before U),
    Route.head_program_right_cast (.conj A B) (rawResidue A B X Y U) ((parametric A B X Y).erase_before U)]
  rfl

theorem source_equation {A B : NormalForm P} {Γ Θ X Y U I J : List (NormalForm P)}
    (f : G P Γ (A::(X++.conj A B::Y))) (g : G P Θ (B::U)) (h : G P I J) (z : At I (.conj A B)) :
    ofTerm (PositionalCut.cut (parent f g) (block A B X Y U).keep h z).denote =
      ofTerm (SequentialConjFirst.routed (.conj A B) (residue A B X Y U)
        (G.cut (SequentialConjFirst.fresh
          (G.cut (SequentialConjFirst.child (SequentialConjFirst.firstChild (parametric A B X Y) f))
            (z.toHead.left h)) g) (z.toHead.left h))).denote := by
  apply (Rules.cut_congr (selected_parent f g) (g:=(z.toHead.left h).denote) rfl).trans
  exact SequentialConjFirst.routed_equation (residue A B X Y U)
    (SequentialConjFirst.firstChild (parametric A B X Y) f) g h z

end BlockedConjFirst
end DosenPetric.Reduced.Gentzen
