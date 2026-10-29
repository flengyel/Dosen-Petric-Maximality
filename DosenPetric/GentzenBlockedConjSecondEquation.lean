module

public import DosenPetric.GentzenBlockedConjSecondData

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace SequentialConjSecond

def routed {K Γ Θ F U I J : List (NormalForm P)} (C : NormalForm P) (p : Route K (F++U))
    (l : G P (I++(Γ++(I++Θ))) (J++(F++(J++U)))) : G P (I++(Γ++Θ)) (J++K) :=
  (((p.head C).program.residual _ _ (p.head_singleFiber C)).prefixFixed J).right (rebuild C l)

theorem routed_count {K Γ Θ F U I J : List (NormalForm P)} (C : NormalForm P) (p : Route K (F++U))
    (l : G P (I++(Γ++(I++Θ))) (J++(F++(J++U)))) : (routed C p l).cutCount = l.cutCount := by
  rw [routed,StructuralProgram.right_count,rebuild_count]

theorem routed_congr {K Γ Θ F U I J : List (NormalForm P)} (C : NormalForm P) (p : Route K (F++U))
    (l l' : G P (I++(Γ++(I++Θ))) (J++(F++(J++U)))) (he : ofTerm l.denote = ofTerm l'.denote) :
    ofTerm (routed C p l).denote = ofTerm (routed C p l').denote := by
  rw [routed,routed,StructuralProgram.right_denote,StructuralProgram.right_denote,rebuild_congr _ _ _ he]

theorem routed_equation {K Γ Θ F U I J : List (NormalForm P)} {A B : NormalForm P}
    (p : Route K (F++U)) (f : G P Γ (A::F)) (g : G P Θ (B::.conj A B::U))
    (h : G P I J) (z : At I (.conj A B)) :
    ofTerm (PositionalCut.cut ((p.head (.conj A B)).program.right (parent f g))
      (.here (.conj A B) K) h z).denote =
      ofTerm (routed (.conj A B) p
        (G.cut (fresh f (G.cut (child g) (z.toHead.left h))) (z.toHead.left h))).denote := by
  apply (CutCommutation.same_right (p.head (.conj A B)).program _ _ (p.head_singleFiber (.conj A B))
    (parent f g) h z).trans
  rw [routed,StructuralProgram.right_denote,StructuralProgram.right_denote]
  exact congrArg (fun k => comp k _) (native_equation f g (z.toHead.left h))

end SequentialConjSecond
namespace BlockedConjSecond

theorem selected_parent {A B : NormalForm P} {Γ Θ F Z T : List (NormalForm P)}
    (f : G P Γ (A::F)) (g : G P Θ (B::(Z++.conj A B::T))) :
    ofTerm ((block A B F Z T).keep.toHead.right (parent f g)).denote =
      ofTerm (((residue A B F Z T).head (.conj A B)).program.right
        (SequentialConjSecond.parent f (SequentialConjSecond.secondChild (parametric A B Z T) g))).denote := by
  have he := SequentialRepair.front_source_denote (block A B F Z T).route (block A B F Z T).keep
    (At.shift F (parametric A B Z T)) (rawResidue A B F Z T)
    (fresh_get A B F Z T) (parametric_get A B F Z T) (fun v => rawResidue_retained A B F Z T v)
    (G.conjR (Δ:=F) (Λ:=Z++.conj A B::T) f g)
  rw [ExchangeScript.right_denote,parent,ContractionBlock.denoteR]
  apply he.trans
  let old := (LogicalDeletion.headUnder [] [.conj A B] (At.shift F (parametric A B Z T))).right
    (G.conjR (Δ:=F) (Λ:=Z++.conj A B::T) f g)
  let canonical := SequentialConjSecond.body f (SequentialConjSecond.secondChild (parametric A B Z T) g)
  have hctx : .conj A B::.conj A B::(At.shift F (parametric A B Z T)).erase =
      .conj A B::.conj A B::(F++(parametric A B Z T).erase) :=
    congrArg (fun xs => (.conj A B : NormalForm P)::.conj A B::xs) (At.erase_shift_at F (parametric A B Z T))
  have hb0 : ofTerm (old.reindex rfl hctx).denote = ofTerm canonical.denote :=
    SequentialConjSecond.selected_body (parametric A B Z T) f g
  have hb := G.reindex_right_cancel_denote hctx old canonical hb0
  have hc := SequentialRepair.headParentRight_congr _ _ hb
  have ht := congrArg (fun k => comp k (((rawResidue A B F Z T).head (.conj A B)).program.arrow .disj)) hc
  rw [StructuralProgram.right_denote]
  apply ht.trans
  rw [← StructuralProgram.right_denote,
    SequentialRepair.headParentRight_reindex (At.erase_shift_at F (parametric A B Z T)),
    Route.head_program_right_cast (.conj A B) (rawResidue A B F Z T) (At.erase_shift_at F (parametric A B Z T))]
  rfl

theorem source_equation {A B : NormalForm P} {Γ Θ F Z T I J : List (NormalForm P)}
    (f : G P Γ (A::F)) (g : G P Θ (B::(Z++.conj A B::T))) (h : G P I J) (z : At I (.conj A B)) :
    ofTerm (PositionalCut.cut (parent f g) (block A B F Z T).keep h z).denote =
      ofTerm (SequentialConjSecond.routed (.conj A B) (residue A B F Z T)
        (G.cut (SequentialConjSecond.fresh f
          (G.cut (SequentialConjSecond.child (SequentialConjSecond.secondChild (parametric A B Z T) g))
            (z.toHead.left h))) (z.toHead.left h))).denote := by
  apply (Rules.cut_congr (selected_parent f g) (g:=(z.toHead.left h).denote) rfl).trans
  exact SequentialConjSecond.routed_equation (residue A B F Z T)
    f (SequentialConjSecond.secondChild (parametric A B Z T) g) h z

end BlockedConjSecond
end DosenPetric.Reduced.Gentzen
