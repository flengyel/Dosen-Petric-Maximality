module
import DosenPetric
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open DosenPetric DosenPetric.Reduced DosenPetric.Reduced.Gentzen
namespace BlockedDisjSecondChecks

section
open BlockedDisjSecond
example {P : Type u} {A B : NormalForm P} {X Z T D E : List (NormalForm P)}
    (f : G P (X++[A]) D) (g : G P ((Z++.disj A B::T)++[B]) E) :
    parent f g = BlockedSource.left2 (.disj A B) (X++Z) T [] (D++E)
      ((BlockedSource.disjLLast f g).reindex (by simp only [List.append_assoc,List.cons_append]) rfl) :=
  BlockedDisjSecond.parent_source f g
end

section
open BlockedDisjSecond
example {P : Type u} {A B : NormalForm P} {X Z T D E I J : List (NormalForm P)}
    (f : G P (X++[A]) D) (g : G P ((Z++.disj A B::T)++[B]) E) (h : G P I J) (z : At J (.disj A B)) :
    ofTerm (PositionalCut.cut h z (parent f g) (block A B X Z T).keep).denote =
      ofTerm (SequentialDisjSecond.rebuild A B (residue A B X Z T)
        (G.cut (z.toHead.right h) (SequentialDisjSecond.fresh (SequentialDisjSecond.firstChild f)
          (G.cut (z.toHead.right h) (SequentialDisjSecond.child
            (SequentialDisjSecond.secondChild (parametric A B Z T) g)))))).denote :=
  BlockedDisjSecond.source_equation f g h z
end

section
open BlockedDisjSecond
example {P : Type u} {A B : NormalForm P} {X Z T D E I J : List (NormalForm P)}
    (f : G P (X++[A]) D) (g : G P ((Z++.disj A B::T)++[B]) E) (h : G P I J) (z : At J (.disj A B))
    (hc : PositionalCut.Clean h z (parent f g) (block A B X Z T).keep) :
    PositionalCut.Clean h z g ((parametric A B Z T).before [B]) ∧
      PositionalCut.rank h z g ((parametric A B Z T).before [B]) <
        PositionalCut.rank h z (parent f g) (block A B X Z T).keep :=
  BlockedDisjSecond.original_descent f g h z hc
end

section
open BlockedDisjSecond
example {P : Type u} {A B : NormalForm P} {X Z T D E I J : List (NormalForm P)}
    (f : G P (X++[A]) D) (g : G P ((Z++.disj A B::T)++[B]) E) (h : G P I J) (z : At J (.disj A B))
    (hc : PositionalCut.Clean h z (parent f g) (block A B X Z T).keep)
    (k : G P (B::((parametric A B Z T).erase++I)) (E++z.erase)) (hk : k.CutFree) (ak : k.Atomized) :
    PositionalCut.Clean h z (SequentialDisjSecond.fresh (SequentialDisjSecond.firstChild f) k)
      (.here (.disj A B) (X++((parametric A B Z T).erase++I))) ∧
      PositionalCut.rank h z (SequentialDisjSecond.fresh (SequentialDisjSecond.firstChild f) k)
        (.here (.disj A B) (X++((parametric A B Z T).erase++I))) <
          PositionalCut.rank h z (parent f g) (block A B X Z T).keep :=
  BlockedDisjSecond.fresh_clean_and_rank f g h z hc k hk ak
end

section
open BlockedDisjSecond
example {P : Type u} {A B : NormalForm P} {X Z T D E I J : List (NormalForm P)}
    (f : G P (X++[A]) D) (g : G P ((Z++.disj A B::T)++[B]) E) (h : G P I J) (z : At J (.disj A B))
    (hc : PositionalCut.Clean h z (BlockedDisjSecond.parent f g) (BlockedDisjSecond.block A B X Z T).keep)
    (ih : ∀ {K L M N : List (NormalForm P)} (b : G P K L) (v : At L (.disj A B))
      (d : G P M N) (w : At M (.disj A B)),
      PositionalCut.rank b v d w <
        PositionalCut.rank h z (BlockedDisjSecond.parent f g) (BlockedDisjSecond.block A B X Z T).keep →
      PositionalCut.Clean b v d w → PositionalCut.Eliminated b v d w) :
    PositionalCut.Eliminated h z (BlockedDisjSecond.parent f g) (BlockedDisjSecond.block A B X Z T).keep :=
  CutCommutation.blockedL_disjunctionSecond_rank_step f g h z hc ih
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

theorem literal_source (l : Literal Nat) (X Z T : List (NormalForm Nat)) :
    PositionalCut.Eliminated (G.identityNF (.disj .bot (.lit l))) (.here _ [])
      (BlockedDisjSecond.parent (X:=X) (Z:=Z) (T:=T) (botTail X)
        (topContext ((Z++.disj .bot (.lit l)::T)++[.lit l])))
      (BlockedDisjSecond.block .bot (.lit l) X Z T).keep := terminal_eliminated _ _ _
example : PositionalCut.Eliminated (G.identityNF (.disj .bot (.lit (.neg 0)))) (.here _ [])
    (BlockedDisjSecond.parent (X:=[]) (Z:=[]) (T:=[]) (botTail [])
      (topContext [.disj .bot (.lit (.neg 0)),.lit (.neg 0)]))
    (BlockedDisjSecond.block .bot (.lit (.neg 0)) [] [] []).keep := literal_source (.neg 0) [] [] []
example : PositionalCut.Eliminated (P:=Empty) (G.identityNF (.disj .bot .top)) (.here _ [])
    (BlockedDisjSecond.parent (X:=[]) (Z:=[]) (T:=[]) (botTail []) (topContext [.disj .bot .top,.top]))
    (BlockedDisjSecond.block .bot .top [] [] []).keep := terminal_eliminated _ _ _
example : PositionalCut.Eliminated (P:=Empty) (G.identityNF (.disj .bot .top)) (.here _ [])
    (BlockedDisjSecond.parent (X:=[.disj .bot .top]) (Z:=[.disj .bot .top]) (T:=[.disj .bot .top])
      (botTail [.disj .bot .top]) (topContext [.disj .bot .top,.disj .bot .top,.disj .bot .top,.top]))
    (BlockedDisjSecond.block .bot .top [.disj .bot .top] [.disj .bot .top] [.disj .bot .top]).keep :=
  terminal_eliminated _ _ _
example : ((BlockedDisjSecond.block (.bot : NormalForm Empty) .top [.disj .bot .top] [] []).route.get
    (.here (.disj .bot .top) [.disj .bot .top,.disj .bot .top])).index = 0 := by rfl
end BlockedDisjSecondChecks

#print axioms DosenPetric.Reduced.Gentzen.LogicalDeletion.headShift_cons_arrow

#print axioms DosenPetric.Reduced.Gentzen.SequentialDisjSecond.native_equation

#print axioms DosenPetric.Reduced.Gentzen.BlockedDisjSecond.source_equation

#print axioms DosenPetric.Reduced.Gentzen.BlockedDisjSecond.original_descent

#print axioms DosenPetric.Reduced.Gentzen.BlockedDisjSecond.fresh_clean_and_rank

#print axioms DosenPetric.Reduced.Gentzen.CutCommutation.blockedL_disjunctionSecond_rank_step
