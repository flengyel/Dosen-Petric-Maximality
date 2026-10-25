module

public import DosenPetric.GentzenDisjunctionSuccedentRanks
public import DosenPetric.GentzenConjunctionAntecedentReducer
public import DosenPetric.GentzenOppositeLogicalBounds

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace BlockedSource

theorem disjLLast_reindex_outputs {Γ Θ F U K L : List (NormalForm P)} {A B : NormalForm P}
    (f : G P (Γ++[A]) F) (g : G P (Θ++[B]) U) (hF : F=K) (hU : U=L) :
    disjLLast (f.reindex rfl hF) (g.reindex rfl hU)=
      (disjLLast f g).reindex rfl (by cases hF; cases hU; rfl) := by
  cases hF; cases hU; rfl
end BlockedSource
namespace W5.DisjunctionSuccedent
variable {A B C : NormalForm P} {F K U L Γ Θ : List (NormalForm P)}
variable (p : ContractionSelection C F K) (q : ContractionSelection C U L)
variable (f : G P (A::Γ) F) (g : G P (B::Θ) U)

def old : G P (.disj A B::(Γ++Θ)) (p.erased++L) := (p.chain q).performR _ (G.disjL f g)
def innerF : G P (A::Γ) K := p.performR _ f
def innerG : G P (B::Θ) L := q.performR _ g
def body : G P ((Γ++Θ)++[.disj A B]) (p.erased++L) :=
  (p.mergeBlock q).applyR (Nat.le_refl 2) _
    (BlockedSource.disjLLast (BlockedSource.tailL A (innerF p f)) (BlockedSource.tailL B (innerG q g)))
def repair : G P (.disj A B::(Γ++Θ)) (p.erased++L) := BlockedSource.headL (.disj A B) (body p q f g)

theorem body_blocked : BlockedR (body p q f g) := by
  have h:=BlockedR.gammaDisj C A B Γ Θ (gaps p.gs) p.tail (gaps q.gs) q.tail
    ((BlockedSource.tailL A (innerF p f)).reindex rfl p.lower.symm)
    ((BlockedSource.tailL B (innerG q g)).reindex rfl q.lower.symm)
  have hm:=BlockedSource.disjLLast_reindex_outputs (BlockedSource.tailL A (innerF p f))
    (BlockedSource.tailL B (innerG q g)) p.lower.symm q.lower.symm
  have he:=h.reindex rfl (p.mergeBlock q).lower
  unfold BlockedSource.right2 at he
  rw [hm] at he
  simpa only [body,ContractionBlock.applyR,ContractionSelection.mergeBlock,G.reindex_trans] using he

theorem denote : ofTerm (repair p q f g).denote=ofTerm (old p q f g).denote := by
  have hs:=p.chain_square q .disj
  change ofTerm (p.chain q).route.coproduct=comp (ofTerm (p.route.parallel q.route).coproduct)
    (ofTerm (p.mergeBlock q).route.coproduct) at hs
  have hrot:=Route.rotations_head .conj (Γ++Θ) (.disj A B)
  change comp (ofTerm (Route.toHead (Γ++Θ) (.disj A B)).product)
    (ofTerm (Route.toTail (Γ++Θ) (.disj A B)).product)=id (ante (.disj A B::(Γ++Θ))) at hrot
  have hb : ofTerm (repair p q f g).denote=
      comp (ofTerm (G.disjL (innerF p f) (innerG q g)).denote) (ofTerm (p.mergeBlock q).route.coproduct) := by
    rw [repair,BlockedSource.headL_denote,body,ContractionBlock.denoteR,BlockedSource.disjLLast_native]
    simp only [Laws.assoc]
    rw [←Laws.assoc (ofTerm (Route.toHead (Γ++Θ) (.disj A B)).product),hrot,Laws.id_comp]
  have hm : ofTerm (G.disjL (innerF p f) (innerG q g)).denote=
      ofTerm (Rules.disjLeft (.comp f.denote p.route.coproduct) (.comp g.denote q.route.coproduct)) :=
    Rules.disjLeft_congr (p.performR_denote _ f) (q.performR_denote _ g)
  have hn:=hm.trans (Route.parallel_disjLeft p.route q.route f.denote g.denote).symm
  rw [hb,hn,Laws.assoc,←hs,old,ContractionSelection.performR_denote]
  rfl

theorem old_count : (old p q f g).cutCount=f.cutCount+g.cutCount := by rw [old,ContractionSelection.performR_count]; rfl
theorem repair_count : (repair p q f g).cutCount=f.cutCount+g.cutCount := by
  simp only [repair,BlockedSource.headL,UnaryCast.exchangeL,G.count_reindex,G.cutCount,body,
    ContractionBlock.countR,BlockedSource.disjLLast_count,BlockedSource.tailL,innerF,innerG,ContractionSelection.performR_count]
end W5.DisjunctionSuccedent
end DosenPetric.Reduced.Gentzen
