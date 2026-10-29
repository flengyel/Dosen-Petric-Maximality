module
import DosenPetric
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open DosenPetric DosenPetric.Reduced DosenPetric.Reduced.Gentzen
namespace BlockedDisjunctionChecks

section
open BlockedDisjunction
example {P : Type u} {A B : NormalForm P} {F X Y : List (NormalForm P)}
    (f : G P F (A::B::(X++.disj A B::Y))) :
    parent f = BlockedSource.right2 (.disj A B) F [] X Y (G.disjR F [] (X++.disj A B::Y) A B f) :=
  BlockedDisjunction.parent_source f
end

section
open BlockedDisjunction
example {P : Type u} {A B : NormalForm P} {F X Y I J : List (NormalForm P)}
    (f : G P F (A::B::(X++.disj A B::Y))) (h : G P I J) (z : At I (.disj A B)) :
    ofTerm (PositionalCut.cut (parent f) (block A B X Y).keep h z).denote =
      ofTerm (SequentialRepair.prefixRouted (.disj A B) (residue A B X Y)
        (G.cut (SequentialDisjunction.fresh (G.cut (nativeChild f) (z.toHead.left h)))
          (z.toHead.left h))).denote :=
  BlockedDisjunction.source_equation f h z
end

section
open BlockedDisjunction
example {P : Type u} {A B : NormalForm P} {F X Y I J : List (NormalForm P)}
    (f : G P F (A::B::(X++.disj A B::Y))) (h : G P I J) (z : At I (.disj A B))
    (hc : PositionalCut.Clean (parent f) (block A B X Y).keep h z) :
    PositionalCut.Clean f (.there (.there (parametric A B X Y))) h z ∧
      PositionalCut.rank f (.there (.there (parametric A B X Y))) h z <
        PositionalCut.rank (parent f) (block A B X Y).keep h z :=
  BlockedDisjunction.original_descent f h z hc
end

section
open SequentialDisjunction
example {P : Type u} {F D J I V : List (NormalForm P)} {A B : NormalForm P}
    (k : G P F (J++A::B::D)) (h : G P I V) (z : At I (.disj A B))
    (hk : k.CutFree) (ak : k.Atomized) (hh : h.CutFree) (ah : h.Atomized) (bh : AllBlockedAt h .left z) :
    PositionalCut.Clean (fresh k) (.here (.disj A B) (J++D)) h z :=
  SequentialDisjunction.fresh_clean k h z hk ak hh ah bh
end

section
open SequentialDisjunction
example {P : Type u} {F D J I V M N : List (NormalForm P)} {A B : NormalForm P}
    (k : G P F (J++A::B::D)) (h : G P I V) (z : At I (.disj A B))
    (old : G P M N) (x : At N (.disj A B)) (hold : 1 < old.rho .right x) :
    PositionalCut.rank (fresh k) (.here (.disj A B) (J++D)) h z < PositionalCut.rank old x h z :=
  SequentialDisjunction.fresh_rank_lt k h z old x hold
end

section
open BlockedDisjunction
example {P : Type u} {A B : NormalForm P} {F X Y I J : List (NormalForm P)}
    (f : G P F (A::B::(X++.disj A B::Y))) (h : G P I J) (z : At I (.disj A B))
    (hc : PositionalCut.Clean (BlockedDisjunction.parent f) (BlockedDisjunction.block A B X Y).keep h z)
    (ih : ∀ {K L M N : List (NormalForm P)} (b : G P K L) (v : At L (.disj A B))
      (d : G P M N) (w : At M (.disj A B)),
      PositionalCut.rank b v d w <
        PositionalCut.rank (BlockedDisjunction.parent f) (BlockedDisjunction.block A B X Y).keep h z →
      PositionalCut.Clean b v d w → PositionalCut.Eliminated b v d w) :
    PositionalCut.Eliminated (BlockedDisjunction.parent f) (BlockedDisjunction.block A B X Y).keep h z :=
  CutCommutation.blockedR_disjunction_rank_step f h z hc ih
end

def bottomContext {P : Type u} : (D : List (NormalForm P)) → G P [.bot] D
  | [] => G.botE
  | A::D => G.headThinR A (bottomContext D)
theorem bottomContext_cf {P : Type u} (D : List (NormalForm P)) : (bottomContext D).CutFree := by
  induction D with
  | nil => rfl
  | cons A D ih => exact G.headThinR_cutFree A _ ih
theorem bottomContext_atomized {P : Type u} (D : List (NormalForm P)) : (bottomContext D).Atomized := by
  induction D with
  | nil => trivial
  | cons A D ih => exact G.headThinR_atomized A _ ih

theorem initial_eliminated {P : Type u} {C : NormalForm P} {D J : List (NormalForm P)}
    (g : G P [.bot] D) (a : At D C) (h : G P [C] J) :
    PositionalCut.Eliminated g a h (.here C []) := by
  refine ⟨bottomContext (J++a.erase),bottomContext_cf _,bottomContext_atomized _,?_⟩
  have he := ((disjDiagonal P).toUnit_unique
    (comp (rightIn .conj .bot) (ofTerm (bottomContext (J++a.erase)).denote))).trans
    ((disjDiagonal P).toUnit_unique
      (comp (rightIn .conj .bot) (ofTerm (PositionalCut.cut g a h (.here C [])).denote))).symm
  have hh := congrArg (fun k => comp (rightOut .conj .bot) k) he
  simpa only [← Laws.assoc,Laws.rightOut_In,Laws.id_comp] using hh

theorem literal_source (l : Literal Nat) (X Y : List (NormalForm Nat)) :
    PositionalCut.Eliminated
      (BlockedDisjunction.parent (X:=X) (Y:=Y)
        (bottomContext (.lit l::.lit l::(X++.disj (.lit l) (.lit l)::Y))))
      (BlockedDisjunction.block (.lit l) (.lit l) X Y).keep
      (G.identityNF (.disj (.lit l) (.lit l))) (.here _ []) :=
  initial_eliminated _ _ _
example : PositionalCut.Eliminated
    (BlockedDisjunction.parent (X:=[]) (Y:=[])
      (bottomContext [.lit (.neg 0),.lit (.neg 0),.disj (.lit (.neg 0)) (.lit (.neg 0))]))
    (BlockedDisjunction.block (.lit (.neg 0)) (.lit (.neg 0)) [] []).keep
    (G.identityNF (.disj (.lit (.neg 0)) (.lit (.neg 0)))) (.here _ []) :=
  literal_source (.neg 0) [] []
example : PositionalCut.Eliminated (P:=Empty)
    (BlockedDisjunction.parent (X:=[]) (Y:=[]) (bottomContext [.top,.bot,.disj .top .bot]))
    (BlockedDisjunction.block .top .bot [] []).keep
    (G.identityNF (.disj .top .bot)) (.here _ []) := initial_eliminated _ _ _
example : PositionalCut.Eliminated (P:=Empty)
    (BlockedDisjunction.parent (X:=[.disj .top .top]) (Y:=[.disj .top .top])
      (bottomContext [.top,.top,.disj .top .top,.disj .top .top,.disj .top .top]))
    (BlockedDisjunction.block .top .top [.disj .top .top] [.disj .top .top]).keep
    (G.identityNF (.disj .top .top)) (.here _ []) := initial_eliminated _ _ _

example : (SequentialRepair.headRoute (P:=Empty) [.top] [.top]).get
    (.here .top [.top,.top]) = .here .top [.top] := by rfl
example : (SequentialRepair.headRoute (P:=Empty) [.top] [.top]).get
    (.there (.here .top [.top])) = .here .top [.top] := by rfl
example : (BlockedDisjunction.block (.top : NormalForm Empty) .top [] []).route.get
    (.here (.disj .top .top) [.disj .top .top]) = (BlockedDisjunction.block .top .top [] []).keep := by rfl
end BlockedDisjunctionChecks

#print axioms DosenPetric.Reduced.Gentzen.SequentialDisjunction.native_equation

#print axioms DosenPetric.Reduced.Gentzen.SequentialDisjunction.source_denote

#print axioms DosenPetric.Reduced.Gentzen.SequentialDisjunction.fresh_rho

#print axioms DosenPetric.Reduced.Gentzen.SequentialDisjunction.fresh_clean

#print axioms DosenPetric.Reduced.Gentzen.SequentialDisjunction.fresh_rank_lt

#print axioms DosenPetric.Reduced.Gentzen.BlockedDisjunction.source_equation

#print axioms DosenPetric.Reduced.Gentzen.BlockedDisjunction.original_descent

#print axioms DosenPetric.Reduced.Gentzen.CutCommutation.blockedR_disjunction_rank_step
