module

public import DosenPetric.GentzenBlockedDisjFirstData

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace SequentialDisjFirst

def rebuild {Y F U D E I R : List (NormalForm P)} (A B : NormalForm P) (p : Route Y (F++U))
    (l : G P (((F++I)++U)++I) (((D++R)++E)++R)) : G P (Y++I) ((D++E)++R) :=
  SequentialRepair.routed (.disj A B) p (adapter (.disj A B) l)

theorem rebuild_count {Y F U D E I R : List (NormalForm P)} (A B : NormalForm P) (p : Route Y (F++U))
    (l : G P (((F++I)++U)++I) (((D++R)++E)++R)) : (rebuild A B p l).cutCount = l.cutCount := by
  rw [rebuild,SequentialRepair.routed_count,adapter_count]

theorem rebuild_congr {Y F U D E I R : List (NormalForm P)} (A B : NormalForm P) (p : Route Y (F++U))
    (l l' : G P (((F++I)++U)++I) (((D++R)++E)++R)) (he : ofTerm l.denote = ofTerm l'.denote) :
    ofTerm (rebuild A B p l).denote = ofTerm (rebuild A B p l').denote := by
  exact SequentialRepair.routed_congr _ _ _ _ (adapter_congr _ _ _ he)

theorem routed_equation {Y F U D E I J : List (NormalForm P)} {A B : NormalForm P}
    (p : Route Y (F++U)) (f : G P (A::.disj A B::F) D) (g : G P (B::U) E)
    (h : G P I J) (z : At J (.disj A B)) :
    ofTerm (PositionalCut.cut h z ((p.head (.disj A B)).program.left (parent f g)) (.here (.disj A B) Y)).denote =
      ofTerm (rebuild A B p (G.cut (z.toHead.right h)
        (fresh (G.cut (z.toHead.right h) (child f)) g))).denote := by
  apply (CutCommutation.same_left (p.head (.disj A B)).program _ _ (p.head_singleFiber (.disj A B))
    h z (parent f g)).trans
  rw [rebuild,SequentialRepair.routed,StructuralProgram.left_denote,StructuralProgram.left_denote]
  exact congrArg (comp _) (native_equation f g (z.toHead.right h))

end SequentialDisjFirst
namespace BlockedDisjFirst

theorem selected_parent {A B : NormalForm P} {X Y Z D E : List (NormalForm P)}
    (f : G P ((X++.disj A B::Y)++[A]) D) (g : G P (Z++[B]) E) :
    ofTerm ((block A B X Y Z).keep.toHead.left (parent f g)).denote =
      ofTerm (((residue A B X Y Z).head (.disj A B)).program.left
        (SequentialDisjFirst.parent (SequentialDisjFirst.firstChild (parametric A B X Y) f)
          (SequentialDisjFirst.secondChild g))).denote := by
  have he := SequentialRepair.terminal_source_denote (block A B X Y Z).route (block A B X Y Z).keep
    ((parametric A B X Y).before Z) (rawResidue A B X Y Z) (first_get A B X Y Z) (second_get A B X Y Z)
    (fun v => (Route.selectedResidual_get _ _ _ _ v).symm) (BlockedSource.disjLLast f g)
  rw [ExchangeScript.left_denote,parent,ContractionBlock.denoteL]
  apply he.trans
  let old := (SequentialLogical.principal ((parametric A B X Y).before Z) (.disj A B)).left
    (BlockedSource.disjLLast f g)
  let canonical := SequentialDisjFirst.body (SequentialDisjFirst.firstChild (parametric A B X Y) f)
    (SequentialDisjFirst.secondChild g)
  have hctx : .disj A B::.disj A B::((parametric A B X Y).before Z).erase =
      .disj A B::.disj A B::((parametric A B X Y).erase++Z) :=
    congrArg (fun xs => (.disj A B : NormalForm P)::(.disj A B)::xs) ((parametric A B X Y).erase_before Z)
  have hb0 : ofTerm (old.reindex hctx rfl).denote = ofTerm canonical.denote :=
    SequentialDisjFirst.selected_body (parametric A B X Y) f g
  have hb := G.reindex_left_cancel_denote hctx old canonical hb0
  have hc := SequentialRepair.headParent_congr _ _ hb
  have ht := congrArg (fun k => comp (((rawResidue A B X Y Z).head (.disj A B)).program.arrow .conj) k) hc
  rw [StructuralProgram.left_denote]
  apply ht.trans
  rw [← StructuralProgram.left_denote,
    SequentialRepair.headParent_reindex ((parametric A B X Y).erase_before Z),
    Route.head_program_left_cast (.disj A B) (rawResidue A B X Y Z) ((parametric A B X Y).erase_before Z)]
  rfl

theorem source_equation {A B : NormalForm P} {X Y Z D E I J : List (NormalForm P)}
    (f : G P ((X++.disj A B::Y)++[A]) D) (g : G P (Z++[B]) E) (h : G P I J) (z : At J (.disj A B)) :
    ofTerm (PositionalCut.cut h z (parent f g) (block A B X Y Z).keep).denote =
      ofTerm (SequentialDisjFirst.rebuild A B (residue A B X Y Z)
        (G.cut (z.toHead.right h)
          (SequentialDisjFirst.fresh (G.cut (z.toHead.right h)
            (SequentialDisjFirst.child (SequentialDisjFirst.firstChild (parametric A B X Y) f)))
            (SequentialDisjFirst.secondChild g)))).denote := by
  apply (Rules.cut_congr (f := (z.toHead.right h).denote) rfl (selected_parent f g)).trans
  exact SequentialDisjFirst.routed_equation (residue A B X Y Z)
    (SequentialDisjFirst.firstChild (parametric A B X Y) f) (SequentialDisjFirst.secondChild g) h z

end BlockedDisjFirst
end DosenPetric.Reduced.Gentzen
