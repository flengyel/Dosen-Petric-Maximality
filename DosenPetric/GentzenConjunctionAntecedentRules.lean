module

public import DosenPetric.GentzenConjunctionAntecedentRanks
public import DosenPetric.GentzenConjunctionInputReducer

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

theorem G.conjR_reindex_sources {F U F' U' Δ Λ : List (NormalForm P)} {A B : NormalForm P}
    (f : G P F (A::Δ)) (g : G P U (B::Λ)) (hF : F=F') (hU : U=U') :
    G.conjR (f.reindex hF rfl) (g.reindex hU rfl)=(G.conjR f g).reindex (by cases hF; cases hU; rfl) rfl := by
  cases hF; cases hU; rfl

namespace W5.ConjunctionAntecedent
variable {A B C : NormalForm P} {F K U L Δ Λ : List (NormalForm P)}
variable (p : ContractionSelection C F K) (q : ContractionSelection C U L)
variable (f : G P F (A::Δ)) (g : G P U (B::Λ))

def old : G P (p.erased++L) (.conj A B::(Δ++Λ)) := (p.chain q).performL _ (G.conjR f g)
def middle : G P (K++L) (.conj A B::(Δ++Λ)) := G.conjR (p.performL _ f) (q.performL _ g)
def repair : G P (p.erased++L) (.conj A B::(Δ++Λ)) :=
  (p.mergeBlock q).applyL (Nat.le_refl 2) _ (middle p q f g)

theorem denote : ofTerm (repair p q f g).denote=ofTerm (old p q f g).denote := by
  have hs:=p.chain_square q .conj
  change ofTerm (p.chain q).route.product=comp (ofTerm (p.mergeBlock q).route.product)
    (ofTerm (p.route.parallel q.route).product) at hs
  have hm : ofTerm (middle p q f g).denote=
      ofTerm (Rules.conjRight (.comp p.route.product f.denote) (.comp q.route.product g.denote)) :=
    Rules.conjRight_congr (p.performL_denote _ f) (q.performL_denote _ g)
  rw [repair,ContractionBlock.denoteL,old,ContractionSelection.performL_denote,hs,Laws.assoc]
  exact congrArg (comp (ofTerm (p.mergeBlock q).route.product))
    (hm.trans (Route.parallel_conjRight p.route q.route f.denote g.denote).symm)

theorem blocked : BlockedL (repair p q f g) := by
  have h:=BlockedL.gammaConj C A B (gaps p.gs) p.tail (gaps q.gs) q.tail Δ Λ
    ((p.performL _ f).reindex p.lower.symm rfl) ((q.performL _ g).reindex q.lower.symm rfl)
  have hm:=G.conjR_reindex_sources (p.performL _ f) (q.performL _ g) p.lower.symm q.lower.symm
  have he:=h.reindex (p.mergeBlock q).lower rfl
  unfold BlockedSource.left2 at he
  rw [hm] at he
  simpa only [repair,ContractionBlock.applyL,ContractionSelection.mergeBlock,G.reindex_trans,middle] using he

theorem old_count : (old p q f g).cutCount=f.cutCount+g.cutCount := by rw [old,ContractionSelection.performL_count]; rfl
theorem repair_count : (repair p q f g).cutCount=f.cutCount+g.cutCount := by
  simp only [repair,ContractionBlock.countL,middle,G.cutCount,ContractionSelection.performL_count]

end W5.ConjunctionAntecedent
end DosenPetric.Reduced.Gentzen
