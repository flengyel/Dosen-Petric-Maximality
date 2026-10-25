module

public import DosenPetric.GentzenNativeLogicalCoordinates
public import DosenPetric.GentzenHeadLogicalContraction

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace W6.SourceLeft

theorem triple_blocked_for {A B : NormalForm P} {F K U L Δ Λ : List (NormalForm P)}
    (p : ContractionSelection (.disj A B) F K) (q : ContractionSelection (.disj A B) U L)
    (f : G P (K++[A]) Δ) (g : G P (L++[B]) Λ) :
    BlockedL ((tripleBlock p q).applyL (triple_bound p q) (Δ++Λ) (BlockedSource.disjLLast f g)) := by
  have h:=BlockedL.disjunctionBoth A B (gaps p.gs) p.tail (gaps q.gs) q.tail Δ Λ
    (f.reindex (congrArg (fun Ξ => Ξ++[A]) p.lower.symm) rfl)
    (g.reindex (congrArg (fun Ξ => Ξ++[B]) q.lower.symm) rfl)
  have hm:=BlockedSource.disjLLast_reindex_inputs f g p.lower.symm q.lower.symm
  have he:=h.reindex (tripleBlock p q).lower rfl
  unfold BlockedSource.left3 at he
  rw [hm] at he
  simpa only [ContractionBlock.applyL,tripleBlock,G.reindex_trans] using he
end W6.SourceLeft

namespace W6.NativeLeft
variable {A B : NormalForm P} {F K U L Δ Λ : List (NormalForm P)}
variable (p : ContractionSelection (.disj A B) F K) (q : ContractionSelection (.disj A B) U L)
variable (f : G P (A::F) Δ) (g : G P (B::U) Λ)

def innerF : G P (A::K) Δ := (p.prependFixed [A]).performL Δ f
def innerG : G P (B::L) Λ := (q.prependFixed [B]).performL Λ g
def old : G P (p.erased++L) (Δ++Λ) :=
  (ContractionSelection.more (p.chain q)).performL (Δ++Λ) (G.disjL f g)
def body : G P (source p q) (Δ++Λ) :=
  (W6.SourceLeft.tripleBlock p q).applyL (W6.SourceLeft.triple_bound p q) _
    (BlockedSource.disjLLast (BlockedSource.tailL A (innerF p f)) (BlockedSource.tailL B (innerG q g)))
def repair : G P (target p q) (Δ++Λ) :=
  UnaryCast.exchangeL (base p q) q.tail [.disj A B] [] (exit_source p q) (exit_target p q) _ (body p q f g)

theorem body_blocked : BlockedL (body p q f g) := W6.SourceLeft.triple_blocked_for p q _ _

theorem denote : ofTerm (repair p q f g).denote=ofTerm (old p q f g).denote := by
  have hs:=p.head_chain_square q .conj
  change ofTerm (ContractionSelection.more (p.chain q)).route.product=
    comp (ofTerm (p.mergeBlock q).selectedHead.route.product)
      (ofTerm ((p.route.parallel q.route).head (.disj A B)).product) at hs
  have hm : ofTerm (G.disjL (innerF p f) (innerG q g)).denote=
      ofTerm (Rules.disjLeft (.comp (p.route.head A).product f.denote)
        (.comp (q.route.head B).product g.denote)) :=
    Rules.disjLeft_congr ((p.prependFixed [A]).performL_denote Δ f)
      ((q.prependFixed [B]).performL_denote Λ g)
  rw [repair,UnaryCast.exchangeL_denote]
  change comp (ofTerm (exitRoute p q).product) (ofTerm (body p q f g).denote)=_
  rw [body,ContractionBlock.denoteL,BlockedSource.disjLLast_native,
    ←Laws.assoc,←Laws.assoc,
    Laws.assoc (ofTerm (exitRoute p q).product) (ofTerm (W6.SourceLeft.tripleBlock p q).route.product)
      (ofTerm (Route.toTail (K++L) (.disj A B)).product),←product_square,hm,←Route.head_disjLeft,
    ←Laws.assoc,←hs,old,ContractionSelection.performL_denote]
  rfl

theorem old_count : (old p q f g).cutCount=f.cutCount+g.cutCount := by
  rw [old,ContractionSelection.performL_count]; rfl
theorem repair_count : (repair p q f g).cutCount=f.cutCount+g.cutCount := by
  simp only [repair,UnaryCast.exchangeL,G.count_reindex,G.cutCount,body,ContractionBlock.countL,
    BlockedSource.disjLLast_count,BlockedSource.tailL,innerF,innerG,ContractionSelection.performL_count]
theorem repair_cutFree : (repair p q f g).CutFree ↔ f.CutFree ∧ g.CutFree := by
  simp only [G.CutFree,repair_count,Nat.add_eq_zero_iff]
theorem repair_atomized : (repair p q f g).Atomized ↔ f.Atomized ∧ g.Atomized := by
  simp only [repair,UnaryCast.exchangeL,G.atomized_reindex,G.Atomized,body,ContractionBlock.atomizedL,
    BlockedSource.disjLLast,BlockedSource.tailL,innerF,innerG,ContractionSelection.performL_atomized]
theorem relation : (repair p q f g).relation=(old p q f g).relation := congrArg occurrenceMap (denote p q f g)

end W6.NativeLeft
end DosenPetric.Reduced.Gentzen
