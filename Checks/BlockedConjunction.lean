module
import DosenPetric
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open DosenPetric DosenPetric.Reduced DosenPetric.Reduced.Gentzen
namespace BlockedConjunctionChecks

section
open BlockedConjunction
example {P : Type u} {A B : NormalForm P} {X Y D : List (NormalForm P)}
    (f : G P ((X++.conj A B::Y)++[A,B]) D) :
    parent f = BlockedSource.left2 (.conj A B) X Y [] D
      ((BlockedSource.conjLLast (X++.conj A B::Y) D A B f).reindex
        (by simp only [List.append_assoc,List.cons_append]) rfl) :=
  BlockedConjunction.parent_source f
end

section
open BlockedConjunction
example {P : Type u} {A B : NormalForm P} {X Y D I J : List (NormalForm P)}
    (f : G P ((X++.conj A B::Y)++[A,B]) D) (h : G P I J) (z : At J (.conj A B)) :
    ofTerm (PositionalCut.cut h z (parent f) (block A B X Y).keep).denote =
      ofTerm (SequentialRepair.routed (.conj A B) (residue A B X Y)
        (G.cut (z.toHead.right h)
          (SequentialConjunction.fresh (G.cut (z.toHead.right h) (nativeChild f))))).denote :=
  BlockedConjunction.source_equation f h z
end

section
open BlockedConjunction
example {P : Type u} {A B : NormalForm P} {X Y D I J : List (NormalForm P)}
    (f : G P ((X++.conj A B::Y)++[A,B]) D) (h : G P I J) (z : At J (.conj A B))
    (hc : PositionalCut.Clean h z (parent f) (block A B X Y).keep) :
    PositionalCut.Clean h z f ((parametric A B X Y).before [A,B]) ∧
      PositionalCut.rank h z f ((parametric A B X Y).before [A,B]) <
        PositionalCut.rank h z (parent f) (block A B X Y).keep :=
  BlockedConjunction.original_descent f h z hc
end

section
open BlockedConjunction
example {P : Type u} {A B : NormalForm P} {X Y D I J : List (NormalForm P)}
    (f : G P ((X++.conj A B::Y)++[A,B]) D) (h : G P I J) (z : At J (.conj A B))
    (hc : PositionalCut.Clean h z (parent f) (block A B X Y).keep)
    (k : G P ((A::B::(parametric A B X Y).erase)++I) (D++z.erase)) (hk : k.CutFree) (ak : k.Atomized) :
    PositionalCut.Clean h z (SequentialConjunction.fresh k) (.here (.conj A B) ((parametric A B X Y).erase++I)) ∧
      PositionalCut.rank h z (SequentialConjunction.fresh k) (.here (.conj A B) ((parametric A B X Y).erase++I)) <
        PositionalCut.rank h z (parent f) (block A B X Y).keep :=
  BlockedConjunction.fresh_clean_and_rank f h z hc k hk ak
end

section
open BlockedConjunction
example {P : Type u} {A B : NormalForm P} {X Y D I J : List (NormalForm P)}
    (f : G P ((X++.conj A B::Y)++[A,B]) D) (h : G P I J) (z : At J (.conj A B))
    (hc : PositionalCut.Clean h z (BlockedConjunction.parent f) (BlockedConjunction.block A B X Y).keep)
    (ih : ∀ {K L M N : List (NormalForm P)} (b : G P K L) (v : At L (.conj A B))
      (d : G P M N) (w : At M (.conj A B)),
      PositionalCut.rank b v d w <
        PositionalCut.rank h z (BlockedConjunction.parent f) (BlockedConjunction.block A B X Y).keep →
      PositionalCut.Clean b v d w → PositionalCut.Eliminated b v d w) :
    PositionalCut.Eliminated h z (BlockedConjunction.parent f) (BlockedConjunction.block A B X Y).keep :=
  CutCommutation.blockedL_conjunction_rank_step f h z hc ih
end

def topContext {P : Type u} : (F : List (NormalForm P)) → G P F [.top]
  | [] => G.topI
  | A::F => G.headThinL A (topContext F)
theorem topContext_cf {P : Type u} (F : List (NormalForm P)) : (topContext F).CutFree := by
  induction F with
  | nil => rfl
  | cons A F ih => exact G.headThinL_cutFree A _ ih
theorem topContext_atomized {P : Type u} (F : List (NormalForm P)) : (topContext F).Atomized := by
  induction F with
  | nil => trivial
  | cons A F ih => exact G.headThinL_atomized A _ ih

theorem terminal_eliminated {P : Type u} {C : NormalForm P} {F I : List (NormalForm P)}
    (h : G P I [C]) (g : G P F [.top]) (a : At F C) :
    PositionalCut.Eliminated h (.here C []) g a := by
  refine ⟨topContext (a.erase++I),topContext_cf _,topContext_atomized _,?_⟩
  have he := ((conjDiagonal P).toUnit_unique
    (comp (ofTerm (topContext (a.erase++I)).denote) (rightOut .disj .top))).trans
    ((conjDiagonal P).toUnit_unique
      (comp (ofTerm (PositionalCut.cut h (.here C []) g a).denote) (rightOut .disj .top))).symm
  have hh := congrArg (fun k => comp k (rightIn .disj .top)) he
  simp only [Laws.assoc,Laws.rightOut_In,Laws.comp_id] at hh
  exact hh.trans (Laws.comp_id _)

theorem literal_source (l : Literal Nat) (X Y : List (NormalForm Nat)) :
    PositionalCut.Eliminated (G.identityNF (.conj (.lit l) (.lit l))) (.here _ [])
      (BlockedConjunction.parent (X:=X) (Y:=Y)
        (topContext ((X++.conj (.lit l) (.lit l)::Y)++[.lit l,.lit l])))
      (BlockedConjunction.block (.lit l) (.lit l) X Y).keep :=
  terminal_eliminated _ _ _
example : PositionalCut.Eliminated (G.identityNF (.conj (.lit (.neg 0)) (.lit (.neg 0)))) (.here _ [])
    (BlockedConjunction.parent (X:=[]) (Y:=[])
      (topContext [.conj (.lit (.neg 0)) (.lit (.neg 0)),.lit (.neg 0),.lit (.neg 0)]))
    (BlockedConjunction.block (.lit (.neg 0)) (.lit (.neg 0)) [] []).keep :=
  literal_source (.neg 0) [] []
example : PositionalCut.Eliminated (P:=Empty) (G.identityNF (.conj .top .bot)) (.here _ [])
    (BlockedConjunction.parent (X:=[]) (Y:=[]) (topContext [.conj .top .bot,.top,.bot]))
    (BlockedConjunction.block .top .bot [] []).keep := terminal_eliminated _ _ _
example : PositionalCut.Eliminated (P:=Empty) (G.identityNF (.conj .top .top)) (.here _ [])
    (BlockedConjunction.parent (X:=[.conj .top .top]) (Y:=[.conj .top .top])
      (topContext [.conj .top .top,.conj .top .top,.conj .top .top,.top,.top]))
    (BlockedConjunction.block .top .top [.conj .top .top] [.conj .top .top]).keep :=
  terminal_eliminated _ _ _

example : (SequentialRepair.headBlock (.conj .top .top : NormalForm Empty) []).route.get
    (.here _ [.conj .top .top]) = .here _ [] := by rfl
example : (SequentialRepair.headBlock (.conj .top .top : NormalForm Empty) []).route.get
    (.there (.here _ [])) = .here _ [] := by rfl
example : (SequentialRepair.tailRoute (P:=Empty) [.top] [.top]).get
    (.there (.there (.here .top []))) = .there (.here .top []) := by rfl
end BlockedConjunctionChecks

#print axioms DosenPetric.Reduced.Gentzen.SequentialConjunction.native_equation

#print axioms DosenPetric.Reduced.Gentzen.SequentialConjunction.source_denote

#print axioms DosenPetric.Reduced.Gentzen.BlockedConjunction.source_equation

#print axioms DosenPetric.Reduced.Gentzen.BlockedConjunction.original_descent

#print axioms DosenPetric.Reduced.Gentzen.BlockedConjunction.fresh_clean_and_rank

#print axioms DosenPetric.Reduced.Gentzen.CutCommutation.blockedL_conjunction_rank_step
