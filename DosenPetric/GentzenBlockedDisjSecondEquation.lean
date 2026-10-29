module

public import DosenPetric.GentzenBlockedDisjSecondData

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace SequentialDisjSecond

def rebuild {Y F U D E I R : List (NormalForm P)} (A B : NormalForm P) (p : Route Y (F++U))
    (l : G P ((F++(U++I))++I) ((D++(E++R))++R)) : G P (Y++I) ((D++E)++R) :=
  SequentialRepair.routed (.disj A B) p (adapter (.disj A B) l)

theorem rebuild_count {Y F U D E I R : List (NormalForm P)} (A B : NormalForm P) (p : Route Y (F++U))
    (l : G P ((F++(U++I))++I) ((D++(E++R))++R)) : (rebuild A B p l).cutCount = l.cutCount := by
  rw [rebuild,SequentialRepair.routed_count,adapter_count]

theorem rebuild_congr {Y F U D E I R : List (NormalForm P)} (A B : NormalForm P) (p : Route Y (F++U))
    (l l' : G P ((F++(U++I))++I) ((D++(E++R))++R)) (he : ofTerm l.denote = ofTerm l'.denote) :
    ofTerm (rebuild A B p l).denote = ofTerm (rebuild A B p l').denote :=
  SequentialRepair.routed_congr _ _ _ _ (adapter_congr _ _ _ he)

theorem routed_equation {Y F U D E I J : List (NormalForm P)} {A B : NormalForm P}
    (p : Route Y (F++U)) (f : G P (A::F) D) (g : G P (B::.disj A B::U) E)
    (h : G P I J) (z : At J (.disj A B)) :
    ofTerm (PositionalCut.cut h z ((p.head (.disj A B)).program.left (parent f g)) (.here (.disj A B) Y)).denote =
      ofTerm (rebuild A B p (G.cut (z.toHead.right h)
        (fresh f (G.cut (z.toHead.right h) (child g))))).denote := by
  apply (CutCommutation.same_left (p.head (.disj A B)).program _ _ (p.head_singleFiber (.disj A B))
    h z (parent f g)).trans
  rw [rebuild,SequentialRepair.routed,StructuralProgram.left_denote,StructuralProgram.left_denote]
  exact congrArg (comp _) (native_equation f g (z.toHead.right h))

end SequentialDisjSecond
namespace BlockedDisjSecond

theorem selected_parent {A B : NormalForm P} {X Z T D E : List (NormalForm P)}
    (f : G P (X++[A]) D) (g : G P ((Z++.disj A B::T)++[B]) E) :
    ofTerm ((block A B X Z T).keep.toHead.left (parent f g)).denote =
      ofTerm (((residue A B X Z T).head (.disj A B)).program.left
        (SequentialDisjSecond.parent (SequentialDisjSecond.firstChild f)
          (SequentialDisjSecond.secondChild (parametric A B Z T) g))).denote := by
  have he := SequentialRepair.terminal_source_denote (block A B X Z T).route (block A B X Z T).keep
    (At.shift X (parametric A B Z T)) (rawResidue A B X Z T) (first_get A B X Z T) (second_get A B X Z T)
    (fun v => (Route.selectedResidual_get _ _ _ _ v).symm) (BlockedSource.disjLLast f g)
  rw [ExchangeScript.left_denote,parent,ContractionBlock.denoteL]
  apply he.trans
  let old := (SequentialLogical.principal (At.shift X (parametric A B Z T)) (.disj A B)).left
    (BlockedSource.disjLLast f g)
  let canonical := SequentialDisjSecond.body (SequentialDisjSecond.firstChild f)
    (SequentialDisjSecond.secondChild (parametric A B Z T) g)
  have hctx : .disj A B::.disj A B::(At.shift X (parametric A B Z T)).erase =
      .disj A B::.disj A B::(X++(parametric A B Z T).erase) :=
    congrArg (fun xs => (.disj A B : NormalForm P)::(.disj A B)::xs) (At.erase_shift_at X (parametric A B Z T))
  have hb0 : ofTerm (old.reindex hctx rfl).denote = ofTerm canonical.denote :=
    SequentialDisjSecond.selected_body (parametric A B Z T) f g
  have hb := G.reindex_left_cancel_denote hctx old canonical hb0
  have hc := SequentialRepair.headParent_congr _ _ hb
  have ht := congrArg (fun k => comp (((rawResidue A B X Z T).head (.disj A B)).program.arrow .conj) k) hc
  rw [StructuralProgram.left_denote]
  apply ht.trans
  rw [← StructuralProgram.left_denote,
    SequentialRepair.headParent_reindex (At.erase_shift_at X (parametric A B Z T)),
    Route.head_program_left_cast (.disj A B) (rawResidue A B X Z T) (At.erase_shift_at X (parametric A B Z T))]
  rfl

theorem source_equation {A B : NormalForm P} {X Z T D E I J : List (NormalForm P)}
    (f : G P (X++[A]) D) (g : G P ((Z++.disj A B::T)++[B]) E) (h : G P I J) (z : At J (.disj A B)) :
    ofTerm (PositionalCut.cut h z (parent f g) (block A B X Z T).keep).denote =
      ofTerm (SequentialDisjSecond.rebuild A B (residue A B X Z T)
        (G.cut (z.toHead.right h) (SequentialDisjSecond.fresh (SequentialDisjSecond.firstChild f)
          (G.cut (z.toHead.right h) (SequentialDisjSecond.child
            (SequentialDisjSecond.secondChild (parametric A B Z T) g)))))).denote := by
  apply (Rules.cut_congr (f := (z.toHead.right h).denote) rfl (selected_parent f g)).trans
  exact SequentialDisjSecond.routed_equation (residue A B X Z T)
    (SequentialDisjSecond.firstChild f) (SequentialDisjSecond.secondChild (parametric A B Z T) g) h z

end BlockedDisjSecond
end DosenPetric.Reduced.Gentzen
