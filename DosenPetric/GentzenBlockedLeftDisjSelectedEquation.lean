module

public import DosenPetric.GentzenBlockedLeftDisjSource

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.BlockedLeftDisj
universe u
variable {P : Type u}

def selectedParallel {K F U D E I R : List (NormalForm P)} {A B C : NormalForm P}
    (x : At K C) (a : At F C) (b : At U C)
    (p : Route x.erase a.erase) (q : Route x.erase b.erase)
    (k : G P ((a.before [A]).erase++I) (D++R))
    (l : G P ((b.before [B]).erase++I) (E++R)) :
    G P ((x.before [.disj A B]).erase++I) ((D++E)++R) :=
  (parallel p q
    (k.reindex (congrArg (fun xs => xs++I) (a.erase_before [A])) rfl)
    (l.reindex (congrArg (fun xs => xs++I) (b.erase_before [B])) rfl)).reindex
      (congrArg (fun xs => xs++I) (x.erase_before [.disj A B])).symm rfl

theorem selectedParallel_count {K F U D E I R : List (NormalForm P)} {A B C : NormalForm P}
    (x : At K C) (a : At F C) (b : At U C)
    (p : Route x.erase a.erase) (q : Route x.erase b.erase)
    (k : G P ((a.before [A]).erase++I) (D++R))
    (l : G P ((b.before [B]).erase++I) (E++R)) :
    (selectedParallel x a b p q k l).cutCount = k.cutCount+l.cutCount := by
  simp only [selectedParallel,G.count_reindex,parallel_count]

theorem selectedParallel_congr {K F U D E I R : List (NormalForm P)} {A B C : NormalForm P}
    (x : At K C) (a : At F C) (b : At U C)
    (p : Route x.erase a.erase) (q : Route x.erase b.erase)
    (k k' : G P ((a.before [A]).erase++I) (D++R))
    (l l' : G P ((b.before [B]).erase++I) (E++R))
    (hk : ofTerm k.denote = ofTerm k'.denote) (hl : ofTerm l.denote = ofTerm l'.denote) :
    ofTerm (selectedParallel x a b p q k l).denote =
      ofTerm (selectedParallel x a b p q k' l').denote := by
  apply G.reindex_congr
  apply parallel_congr
  · exact G.reindex_congr _ _ hk
  · exact G.reindex_congr _ _ hl

theorem selected_equation {K F U D E I J : List (NormalForm P)} {A B C : NormalForm P}
    (r : Route K (F++U)) (x : At K C) (a : At F C) (b : At U C)
    (p : Route x.erase a.erase) (q : Route x.erase b.erase)
    (ha : r.firstBlock.get a = x) (hb : r.secondBlock.get b = x)
    (hp : ∀ {V : NormalForm P} (v : At a.erase V),
      r.firstBlock.get (a.retain v) = x.retain (p.get v))
    (hq : ∀ {V : NormalForm P} (v : At b.erase V),
      r.secondBlock.get (b.retain v) = x.retain (q.get v))
    (f : G P (F++[A]) D) (g : G P (U++[B]) E)
    (t : G P (K++[.disj A B]) (D++E))
    (ht : ofTerm t.denote = comp ((r.parallel (Route.identity [.disj A B])).sideArrow .conj)
      (ofTerm (BlockedSource.disjLLast f g).denote))
    (h : G P I J) (z : At J C) :
    ofTerm (PositionalCut.cut h z t (x.before [.disj A B])).denote =
      ofTerm (selectedParallel x a b p q (PositionalCut.cut h z f (a.before [A]))
        (PositionalCut.cut h z g (b.before [B]))).denote := by
  apply G.reindex_left_cancel_denote
    (congrArg (fun xs => xs++I) (x.erase_before [.disj A B]))
  rw [PositionalCut.reindex_residues h z t (x.before [.disj A B]) rfl
    (x.erase_before [.disj A B])]
  change ofTerm (G.cut (z.toHead.right h) ((LogicalDeletion.headBefore x [.disj A B]).left t)).denote =
    ofTerm (parallel p q
      ((PositionalCut.cut h z f (a.before [A])).reindex
        (congrArg (fun xs => xs++I) (a.erase_before [A])) rfl)
      ((PositionalCut.cut h z g (b.before [B])).reindex
        (congrArg (fun xs => xs++I) (b.erase_before [B])) rfl)).denote
  have he : ofTerm ((LogicalDeletion.headBefore x [.disj A B]).left t).denote =
      ofTerm (headParent p q ((LogicalDeletion.headBefore a [A]).left f)
        ((LogicalDeletion.headBefore b [B]).left g)).denote := by
    rw [ExchangeScript.left_denote,ht]
    exact source_denote r x a b p q ha hb hp hq f g
  apply (Rules.cut_congr rfl he).trans
  rw [PositionalCut.reindex_residues h z f (a.before [A]) rfl (a.erase_before [A]),
    PositionalCut.reindex_residues h z g (b.before [B]) rfl (b.erase_before [B])]
  exact headParent_equation p q (z.toHead.right h)
    ((LogicalDeletion.headBefore a [A]).left f) ((LogicalDeletion.headBefore b [B]).left g)

end DosenPetric.Reduced.Gentzen.BlockedLeftDisj
