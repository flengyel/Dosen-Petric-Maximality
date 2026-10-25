module

public import DosenPetric.GentzenSourceSingletonExclusions
public import DosenPetric.GentzenOneHeadDisjunction

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace ContractionSelection
variable {C : NormalForm P} {F : List (NormalForm P)}

theorem singleton_terminal_block (p : ContractionSelection C F F) (h : p.arity=1) :
    (p.chain (.last [])).block=p.retainedLastBlock := by
  apply ContractionBlock.ext_data
  · rfl
  · change (p.chain (.last [])).gs=[gaps p.gs,p.tail]
    rw [p.chain_gs]
    simp only [gs,p.singleton_rest h,gaps,List.append_nil,List.cons_append,List.nil_append,first,rest]
  · exact p.chain_tail (.last [])
end ContractionSelection
namespace W6.SourceOne
variable {A B : NormalForm P} {F K U L Δ Λ : List (NormalForm P)}
section First
variable (p : ContractionSelection (.disj A B) F K)

theorem blockedFirst (f : G P (K++[A]) Δ) (g : G P (U++[B]) Λ) :
    BlockedL ((p.extend U).retainedLastBlock.applyL (p.extend U).retainedLast_bound _ (BlockedSource.disjLLast f g)) := by
  have h:=BlockedL.disjunctionFirst A B (gaps p.gs) p.tail U Δ Λ
    (f.reindex (congrArg (fun Ξ=>Ξ++[A]) p.lower.symm) rfl) g
  have hm:=BlockedSource.disjLLast_reindex_inputs f g p.lower.symm rfl
  simp only [G.reindex_refl] at hm
  have he:=h.reindex (W6.OneHeadDisjunction.blockFirst (U:=U) p).lower rfl
  unfold BlockedSource.left2 at he
  rw [hm] at he
  have hc : BlockedL ((W6.OneHeadDisjunction.blockFirst (U:=U) p).applyL (Nat.le_refl 2) _ (BlockedSource.disjLLast f g)) := by
    simpa only [ContractionBlock.applyL,W6.OneHeadDisjunction.blockFirst,G.reindex_trans] using he
  rw [←ContractionBlock.applyL_congr (W6.OneHeadDisjunction.block_eqFirst (U:=U) p) (Nat.le_refl 2)
    (p.extend U).retainedLast_bound (Δ++Λ) (BlockedSource.disjLLast f g)]
  exact hc

theorem oldFirst_singleton_blocked (hp : p.arity=1) (f : G P (F++[A]) Δ) (g : G P (U++[B]) Λ) :
    BlockedL (((p.extend U).chain (.last [])).performL (Δ++Λ) (BlockedSource.disjLLast f g)) := by
  cases p.singleton_endpoints hp
  have hr : (p.extend U).arity=1 := (p.extend_arity U).trans hp
  have hn : 2≤((p.extend U).chain (.last [])).arity := by rw [ContractionSelection.chain_count,hr]; exact Nat.le_refl 2
  rw [ContractionSelection.performL_eq_apply _ hn]
  rw [ContractionBlock.applyL_congr ((p.extend U).singleton_terminal_block hr) _ (p.extend U).retainedLast_bound _ _]
  exact blockedFirst p f g
end First
section Second
variable (q : ContractionSelection (.disj A B) U L)

theorem blockedSecond (f : G P (F++[A]) Δ) (g : G P (L++[B]) Λ) :
    BlockedL ((q.prependFixed F).retainedLastBlock.applyL (q.prependFixed F).retainedLast_bound _ (BlockedSource.disjLLast f g)) := by
  have h:=BlockedL.disjunctionSecond A B F (gaps q.gs) q.tail Δ Λ
    f (g.reindex (congrArg (fun Ξ=>Ξ++[B]) q.lower.symm) rfl)
  have hm:=BlockedSource.disjLLast_reindex_inputs f g rfl q.lower.symm
  simp only [G.reindex_refl] at hm
  have he:=h.reindex (W6.OneHeadDisjunction.blockSecond (F:=F) q).lower rfl
  unfold BlockedSource.left2 at he
  rw [hm] at he
  have hc : BlockedL ((W6.OneHeadDisjunction.blockSecond (F:=F) q).applyL (Nat.le_refl 2) _ (BlockedSource.disjLLast f g)) := by
    simpa only [ContractionBlock.applyL,W6.OneHeadDisjunction.blockSecond,G.reindex_trans] using he
  rw [←ContractionBlock.applyL_congr (W6.OneHeadDisjunction.block_eqSecond (F:=F) q) (Nat.le_refl 2)
    (q.prependFixed F).retainedLast_bound (Δ++Λ) (BlockedSource.disjLLast f g)]
  exact hc

theorem oldSecond_singleton_blocked (hq : q.arity=1) (f : G P (F++[A]) Δ) (g : G P (U++[B]) Λ) :
    BlockedL (((q.prependFixed F).chain (.last [])).performL (Δ++Λ) (BlockedSource.disjLLast f g)) := by
  cases q.singleton_endpoints hq
  have hr : (q.prependFixed F).arity=1 := (q.prepend_arity F).trans hq
  have hn : 2≤((q.prependFixed F).chain (.last [])).arity := by rw [ContractionSelection.chain_count,hr]; exact Nat.le_refl 2
  rw [ContractionSelection.performL_eq_apply _ hn]
  rw [ContractionBlock.applyL_congr ((q.prependFixed F).singleton_terminal_block hr) _ (q.prependFixed F).retainedLast_bound _ _]
  exact blockedSecond q f g
end Second
end W6.SourceOne
end DosenPetric.Reduced.Gentzen
