module
import DosenPetric
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open DosenPetric DosenPetric.Reduced DosenPetric.Reduced.Gentzen
namespace BlockedDisjFirstChecks

section
open BlockedDisjFirst
example {P : Type u} {A B : NormalForm P} {X Y Z D E : List (NormalForm P)}
    (f : G P ((X++.disj A B::Y)++[A]) D) (g : G P (Z++[B]) E) :
    parent f g = BlockedSource.left2 (.disj A B) X (Y++Z) [] (D++E)
      ((BlockedSource.disjLLast f g).reindex (by simp only [List.append_assoc,List.cons_append]) rfl) :=
  BlockedDisjFirst.parent_source f g
end

section
open BlockedDisjFirst
example {P : Type u} {A B : NormalForm P} {X Y Z D E I J : List (NormalForm P)}
    (f : G P ((X++.disj A B::Y)++[A]) D) (g : G P (Z++[B]) E) (h : G P I J) (z : At J (.disj A B)) :
    ofTerm (PositionalCut.cut h z (parent f g) (block A B X Y Z).keep).denote =
      ofTerm (SequentialDisjFirst.rebuild A B (residue A B X Y Z)
        (G.cut (z.toHead.right h)
          (SequentialDisjFirst.fresh (G.cut (z.toHead.right h)
            (SequentialDisjFirst.child (SequentialDisjFirst.firstChild (parametric A B X Y) f)))
            (SequentialDisjFirst.secondChild g)))).denote :=
  BlockedDisjFirst.source_equation f g h z
end

section
open BlockedDisjFirst
example {P : Type u} {A B : NormalForm P} {X Y Z D E I J : List (NormalForm P)}
    (f : G P ((X++.disj A B::Y)++[A]) D) (g : G P (Z++[B]) E) (h : G P I J) (z : At J (.disj A B))
    (hc : PositionalCut.Clean h z (parent f g) (block A B X Y Z).keep) :
    PositionalCut.Clean h z f ((parametric A B X Y).before [A]) ∧
      PositionalCut.rank h z f ((parametric A B X Y).before [A]) <
        PositionalCut.rank h z (parent f g) (block A B X Y Z).keep :=
  BlockedDisjFirst.original_descent f g h z hc
end

section
open BlockedDisjFirst
example {P : Type u} {A B : NormalForm P} {X Y Z D E I J : List (NormalForm P)}
    (f : G P ((X++.disj A B::Y)++[A]) D) (g : G P (Z++[B]) E) (h : G P I J) (z : At J (.disj A B))
    (hc : PositionalCut.Clean h z (parent f g) (block A B X Y Z).keep)
    (k : G P (A::((parametric A B X Y).erase++I)) (D++z.erase)) (hk : k.CutFree) (ak : k.Atomized) :
    PositionalCut.Clean h z (SequentialDisjFirst.fresh k (SequentialDisjFirst.secondChild g))
      (.here (.disj A B) (((parametric A B X Y).erase++I)++Z)) ∧
      PositionalCut.rank h z (SequentialDisjFirst.fresh k (SequentialDisjFirst.secondChild g))
        (.here (.disj A B) (((parametric A B X Y).erase++I)++Z)) <
          PositionalCut.rank h z (parent f g) (block A B X Y Z).keep :=
  BlockedDisjFirst.fresh_clean_and_rank f g h z hc k hk ak
end

section
open BlockedDisjFirst
example {P : Type u} {A B : NormalForm P} {X Y Z D E I R : List (NormalForm P)}
    (g : G P (Z++[B]) E) (k : G P (A::((parametric A B X Y).erase++I)) (D++R)) :
    (SequentialDisjFirst.fresh k (SequentialDisjFirst.secondChild g)).rho .left
      (.here (.disj A B) (((parametric A B X Y).erase++I)++Z)) = 1 :=
  BlockedDisjFirst.fresh_principal_rank g k
end

section
open BlockedDisjFirst
example {P : Type u} {A B : NormalForm P} {X Y Z D E I J : List (NormalForm P)}
    (g : G P (Z++[B]) E) (h : G P I J) (z : At J (.disj A B))
    (k : G P (A::((parametric A B X Y).erase++I)) (D++z.erase)) :
    PositionalCut.rank h z (SequentialDisjFirst.fresh k (SequentialDisjFirst.secondChild g))
      (.here (.disj A B) (((parametric A B X Y).erase++I)++Z)) = h.rho .right z+1 :=
  BlockedDisjFirst.fresh_total_rank g h z k
end

section
open BlockedDisjFirst
example {P : Type u} {A B : NormalForm P} {X Y Z D E I J : List (NormalForm P)}
    (g : G P (Z++[B]) E) (h : G P I J) (z : At J (.disj A B))
    (k : G P (A::((parametric A B X Y).erase++I)) (D++z.erase)) :
    2 ≤ PositionalCut.rank h z (SequentialDisjFirst.fresh k (SequentialDisjFirst.secondChild g))
      (.here (.disj A B) (((parametric A B X Y).erase++I)++Z)) :=
  BlockedDisjFirst.fresh_total_rank_ge_two g h z k
end

section
open BlockedDisjFirst
example {P : Type u} {A B : NormalForm P} {X Y Z D E I J : List (NormalForm P)}
    (f : G P ((X++.disj A B::Y)++[A]) D) (g : G P (Z++[B]) E) (h : G P I J) (z : At J (.disj A B))
    (hc : PositionalCut.Clean h z (BlockedDisjFirst.parent f g) (BlockedDisjFirst.block A B X Y Z).keep)
    (ih : ∀ {K L M N : List (NormalForm P)} (b : G P K L) (v : At L (.disj A B))
      (d : G P M N) (w : At M (.disj A B)),
      PositionalCut.rank b v d w <
        PositionalCut.rank h z (BlockedDisjFirst.parent f g) (BlockedDisjFirst.block A B X Y Z).keep →
      PositionalCut.Clean b v d w → PositionalCut.Eliminated b v d w) :
    PositionalCut.Eliminated h z (BlockedDisjFirst.parent f g) (BlockedDisjFirst.block A B X Y Z).keep :=
  CutCommutation.blockedL_disjunctionFirst_rank_step f g h z hc ih
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

def botTail {P : Type u} : (Z : List (NormalForm P)) → G P (Z++[.bot]) []
  | [] => G.botE
  | A::Z => G.headThinL A (botTail Z)
theorem botTail_cf {P : Type u} (Z : List (NormalForm P)) : (botTail Z).CutFree := by
  induction Z with
  | nil => rfl
  | cons A Z ih => exact G.headThinL_cutFree A _ ih
theorem botTail_atomized {P : Type u} (Z : List (NormalForm P)) : (botTail Z).Atomized := by
  induction Z with
  | nil => trivial
  | cons A Z ih => exact G.headThinL_atomized A _ ih

theorem literal_source (l : Literal Nat) (X Y Z : List (NormalForm Nat)) :
    PositionalCut.Eliminated (G.identityNF (.disj (.lit l) .bot)) (.here _ [])
      (BlockedDisjFirst.parent (X:=X) (Y:=Y) (Z:=Z)
        (topContext ((X++.disj (.lit l) .bot::Y)++[.lit l])) (botTail Z))
      (BlockedDisjFirst.block (.lit l) .bot X Y Z).keep :=
  terminal_eliminated _ _ _
example : PositionalCut.Eliminated (G.identityNF (.disj (.lit (.neg 0)) .bot)) (.here _ [])
    (BlockedDisjFirst.parent (X:=[]) (Y:=[]) (Z:=[])
      (topContext [.disj (.lit (.neg 0)) .bot,.lit (.neg 0)]) (botTail []))
    (BlockedDisjFirst.block (.lit (.neg 0)) .bot [] [] []).keep :=
  literal_source (.neg 0) [] [] []
example : PositionalCut.Eliminated (P:=Empty) (G.identityNF (.disj .top .bot)) (.here _ [])
    (BlockedDisjFirst.parent (X:=[]) (Y:=[]) (Z:=[]) (topContext [.disj .top .bot,.top]) (botTail []))
    (BlockedDisjFirst.block .top .bot [] [] []).keep := terminal_eliminated _ _ _
example : PositionalCut.Eliminated (P:=Empty) (G.identityNF (.disj .top .bot)) (.here _ [])
    (BlockedDisjFirst.parent (X:=[.disj .top .bot]) (Y:=[.disj .top .bot]) (Z:=[.disj .top .bot])
      (topContext [.disj .top .bot,.disj .top .bot,.disj .top .bot,.top]) (botTail [.disj .top .bot]))
    (BlockedDisjFirst.block .top .bot [.disj .top .bot] [.disj .top .bot] [.disj .top .bot]).keep :=
  terminal_eliminated _ _ _
example : (BlockedSource.disjLLast (Γ:=[]) (Θ:=[]) (G.topIdentity (P:=Empty)) G.topIdentity).rho
    .left (.here (.disj .top .top) []) = 2 :=
  BlockedSource.disjLLast_rank_principal _ _
example : (G.disjL (G.topIdentity (P:=Empty)) G.topIdentity).rho
    .left (.here (.disj .top .top) []) = 1 := G.rho_disjL_principal _ _
end BlockedDisjFirstChecks

#print axioms DosenPetric.Reduced.Gentzen.SequentialDisjFirst.native_equation

#print axioms DosenPetric.Reduced.Gentzen.BlockedDisjFirst.source_equation

#print axioms DosenPetric.Reduced.Gentzen.BlockedDisjFirst.original_descent

#print axioms DosenPetric.Reduced.Gentzen.BlockedDisjFirst.fresh_clean_and_rank

#print axioms DosenPetric.Reduced.Gentzen.BlockedDisjFirst.fresh_principal_rank

#print axioms DosenPetric.Reduced.Gentzen.BlockedDisjFirst.fresh_total_rank

#print axioms DosenPetric.Reduced.Gentzen.BlockedDisjFirst.fresh_total_rank_ge_two

#print axioms DosenPetric.Reduced.Gentzen.CutCommutation.blockedL_disjunctionFirst_rank_step
