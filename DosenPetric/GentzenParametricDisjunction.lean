module

public import DosenPetric.GentzenTailExtendedBlock
public import DosenPetric.GentzenDisjunctionSuccedentBoth
public import DosenPetric.GentzenOneDisjunctionAntecedentReducer

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace Route
theorem head_product_factor {F K : List (NormalForm P)} (D : NormalForm P) (r : Route K F) :
    ofTerm (r.head D).product=comp (ofTerm (toHead K D).product)
      (comp (ofTerm (r.parallel (identity [D])).product) (ofTerm (toTail F D).product)) := by
  apply product_positions
  intro E a
  rw [product_get,Laws.assoc,Laws.assoc,product_get,product_get,product_get]
  cases a with
  | here => rw [head_here,toTail_here,parallel_shift,get_identity,toHead_last]
  | there a => rw [head_there,toTail_there,parallel_before,toHead_before]
end Route
namespace W5.ParametricDisjunction
variable {A B C : NormalForm P} {F K U L Δ Λ : List (NormalForm P)}
variable (p : ContractionSelection C F K) (q : ContractionSelection C U L)
variable (f : G P (A::F) Δ) (g : G P (B::U) Λ)

abbrev block := (p.mergeBlock q).extend [.disj A B]
theorem block_bound : 2≤(block (A:=A) (B:=B) p q).gs.length := Nat.le_refl 2

def old : G P (.disj A B::(p.erased++L)) (Δ++Λ) :=
  (ContractionSelection.fixed (.disj A B) (p.chain q)).performL _ (G.disjL f g)
def innerF : G P (A::K) Δ := (p.prependFixed [A]).performL _ f
def innerG : G P (B::L) Λ := (q.prependFixed [B]).performL _ g
def body : G P ((p.erased++L)++[.disj A B]) (Δ++Λ) :=
  (block p q).applyL (block_bound p q) _
    (BlockedSource.disjLLast (BlockedSource.tailL A (innerF p f)) (BlockedSource.tailL B (innerG q g)))
def repair : G P (.disj A B::(p.erased++L)) (Δ++Λ) :=
  BlockedSource.headL (.disj A B) (body p q f g)

theorem body_blocked : BlockedL (body p q f g) := by
  have h:=BlockedL.gammaDisj C A B (gaps p.gs) p.tail (gaps q.gs) q.tail Δ Λ
    ((BlockedSource.tailL A (innerF p f)).reindex (congrArg (fun Ξ=>Ξ++[A]) p.lower.symm) rfl)
    ((BlockedSource.tailL B (innerG q g)).reindex (congrArg (fun Ξ=>Ξ++[B]) q.lower.symm) rfl)
  have hm:=BlockedSource.disjLLast_reindex_inputs (BlockedSource.tailL A (innerF p f))
    (BlockedSource.tailL B (innerG q g)) p.lower.symm q.lower.symm
  have he:=h.reindex (block p q).lower rfl
  unfold BlockedSource.left2 at he
  rw [hm] at he
  simpa only [body,ContractionBlock.applyL,block,ContractionBlock.extend,ContractionSelection.mergeBlock,
    G.reindex_trans,List.append_assoc,List.cons_append] using he

theorem denote : ofTerm (repair p q f g).denote=ofTerm (old p q f g).denote := by
  have hs:=p.chain_square q .conj
  change ofTerm (p.chain q).route.product=comp (ofTerm (p.mergeBlock q).route.product)
    (ofTerm (p.route.parallel q.route).product) at hs
  have hf:=Route.head_product_factor (.disj A B) (p.mergeBlock q).route
  rw [←Laws.assoc] at hf
  have hn:=Route.head_disjLeft p.route q.route f.denote g.denote
  have hm : ofTerm (G.disjL (innerF p f) (innerG q g)).denote=
      ofTerm (Rules.disjLeft (.comp (p.route.head A).product f.denote) (.comp (q.route.head B).product g.denote)) :=
    Rules.disjLeft_congr ((p.prependFixed [A]).performL_denote _ f) ((q.prependFixed [B]).performL_denote _ g)
  have hh : ofTerm ((p.chain q).route.head (.disj A B)).product=
      comp (ofTerm ((p.mergeBlock q).route.head (.disj A B)).product)
        (ofTerm ((p.route.parallel q.route).head (.disj A B)).product) := by
    apply product_positions
    intro E a
    rw [Route.product_get,Laws.assoc,Route.product_get,Route.product_get]
    cases a with
    | here => simp only [Route.head_here]
    | there a =>
      rw [Route.head_there,Route.head_there,Route.head_there]
      have he:=congrArg (fun r => r) (p.chain_get q a)
      rw [he]
  rw [repair,BlockedSource.headL_denote,body,ContractionBlock.denoteL,BlockedSource.disjLLast_native]
  rw [block,ContractionBlock.extend_route,←Laws.assoc,←Laws.assoc,←hf,hm,←hn,←Laws.assoc,←hh,
    old,ContractionSelection.performL_denote]
  rfl

theorem old_count : (old p q f g).cutCount=f.cutCount+g.cutCount := by
  rw [old,ContractionSelection.performL_count]; rfl
theorem repair_count : (repair p q f g).cutCount=f.cutCount+g.cutCount := by
  simp only [repair,BlockedSource.headL,UnaryCast.exchangeL,G.count_reindex,G.cutCount,body,
    ContractionBlock.countL,BlockedSource.disjLLast_count,BlockedSource.tailL,innerF,innerG,ContractionSelection.performL_count]
end W5.ParametricDisjunction
end DosenPetric.Reduced.Gentzen
