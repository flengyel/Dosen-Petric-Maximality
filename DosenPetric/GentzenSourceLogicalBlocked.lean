module

public import DosenPetric.GentzenSourceLogicalContraction
public import DosenPetric.GentzenBlockedEntryFrames
public import DosenPetric.GentzenMixSelectionReducer

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace ContractionSelection
variable {C : NormalForm P} {F K U L : List (NormalForm P)}

theorem performL_eq_apply (p : ContractionSelection C F K) (hn : 2≤p.arity)
    {Δ : List (NormalForm P)} (f : G P F Δ) :
    p.performL Δ f=p.block.applyL (p.blockArity hn) Δ f := by
  unfold performL
  rw [dite_eq_left hn]

theorem sourceRetained_gs (p : ContractionSelection C F K) (q : ContractionSelection C U L) :
    (p.sourceRetained q).gs=[gaps p.gs,p.tail++gaps q.gs,q.tail] := by
  rw [sourceRetained,gs_cast]
  change (p.retainChain (q.retainChain (.last []))).first::
    (p.retainChain (q.retainChain (.last []))).rest = _
  rw [retain_first,retain_rest,retain_first,retain_rest]
  simp only [first,rest,List.append_nil]

theorem sourceRetained_tail (p : ContractionSelection C F K) (q : ContractionSelection C U L) :
    (p.sourceRetained q).tail=[] := by rw [sourceRetained,tail_cast,retain_tail,retain_tail]; rfl
end ContractionSelection

namespace BlockedSource

theorem disjLLast_reindex_inputs {F U F' U' Δ Λ : List (NormalForm P)} {A B : NormalForm P}
    (f : G P (F++[A]) Δ) (g : G P (U++[B]) Λ) (hF : F=F') (hU : U=U') :
    disjLLast (f.reindex (congrArg (fun Ξ => Ξ++[A]) hF) rfl)
      (g.reindex (congrArg (fun Ξ => Ξ++[B]) hU) rfl) =
    (disjLLast f g).reindex (by cases hF; cases hU; rfl) rfl := by
  cases hF; cases hU; rfl
end BlockedSource

namespace W6.SourceLeft
variable {A B : NormalForm P} {F K U L Δ Λ : List (NormalForm P)}
variable (p : ContractionSelection (.disj A B) F K) (q : ContractionSelection (.disj A B) U L)
variable (f : G P (F++[A]) Δ) (g : G P (U++[B]) Λ)

def tripleBlock : ContractionBlock P ((K++L)++[.disj A B]) (p.erased++(q.erased++[.disj A B])) where
  C := .disj A B
  gs := [gaps p.gs,p.tail++gaps q.gs,q.tail]
  tail := []
  upper := by
    calc
      _ = ((gaps p.gs++.disj A B::p.tail)++(gaps q.gs++.disj A B::q.tail))++[.disj A B] := by
        simp only [repeated,List.nil_append,List.append_assoc,List.cons_append]
      _ = (K++L)++[.disj A B] := by rw [p.lower,q.lower]
  lower := by
    rw [p.erased_eq,q.erased_eq]
    simp only [gaps,List.append_nil,List.append_assoc]

theorem triple_block : (p.sourceRetained q).block=tripleBlock p q :=
  ContractionSelection.block_match _ _ rfl (p.sourceRetained_gs q) (p.sourceRetained_tail q)

theorem triple_bound : 2≤(tripleBlock p q).gs.length := by change 2≤3; decide

theorem repair_eq_triple : repair p q f g=(tripleBlock p q).applyL (triple_bound p q) (Δ++Λ) (middle p q f g) := by
  have hn : 2≤(p.sourceRetained q).arity := by rw [ContractionSelection.sourceRetained_arity]; decide
  rw [repair,ContractionSelection.performL_eq_apply _ hn]
  exact ContractionBlock.applyL_congr (triple_block p q) _ _ _ _

theorem repair_blocked : BlockedL (repair p q f g) := by
  have h := BlockedL.disjunctionBoth A B (gaps p.gs) p.tail (gaps q.gs) q.tail Δ Λ
    (((p.extend [A]).performL Δ f).reindex (congrArg (fun Ξ => Ξ++[A]) p.lower.symm) rfl)
    (((q.extend [B]).performL Λ g).reindex (congrArg (fun Ξ => Ξ++[B]) q.lower.symm) rfl)
  have hm := BlockedSource.disjLLast_reindex_inputs
    ((p.extend [A]).performL Δ f) ((q.extend [B]).performL Λ g) p.lower.symm q.lower.symm
  have he := h.reindex (tripleBlock p q).lower rfl
  unfold BlockedSource.left3 at he
  rw [hm] at he
  rw [repair_eq_triple]
  simpa only [ContractionBlock.applyL,tripleBlock,BlockedSource.left3,
    G.reindex_trans,middle] using he

end W6.SourceLeft
end DosenPetric.Reduced.Gentzen
