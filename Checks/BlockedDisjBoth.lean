module
import DosenPetric
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open DosenPetric DosenPetric.Reduced DosenPetric.Reduced.Gentzen
namespace BlockedDisjBothChecks

section
open BlockedDisjBoth SequentialDisjBoth
example {P : Type u} {Y F H D E I R : List (NormalForm P)} {A B : NormalForm P}
    (p : Route Y F) (q : Route Y H) (h : G P I (.disj A B::R))
    (f : G P (.disj A B::(F++[A])) D) (g : G P (.disj A B::(H++[B])) E) :
    ofTerm (G.cut h (parent p q f g)).denote =
      ofTerm (rebuild (.disj A B) p q (G.cut h (fresh (G.cut h f) (G.cut h g)))).denote :=
  SequentialDisjBoth.native_equation p q h f g
end

section
open BlockedDisjBoth SequentialDisjBoth
example {P : Type u} {A B : NormalForm P} {X Y Z T D E : List (NormalForm P)}
    (f : G P ((X++.disj A B::Y)++[A]) D) (g : G P ((Z++.disj A B::T)++[B]) E) :
    parent f g = BlockedSource.left3 (.disj A B) X (Y++Z) T [] (D++E)
      ((BlockedSource.disjLLast f g).reindex (by simp only [List.append_assoc,List.cons_append]) rfl) :=
  BlockedDisjBoth.parent_source f g
end

section
open BlockedDisjBoth SequentialDisjBoth
example {P : Type u} {A B : NormalForm P} {X Y Z T D E I J : List (NormalForm P)}
    (f : G P ((X++.disj A B::Y)++[A]) D) (g : G P ((Z++.disj A B::T)++[B]) E)
    (h : G P I J) (z : At J (.disj A B)) :
    ofTerm (PositionalCut.cut h z (parent f g) (block A B X Y Z T).keep).denote =
      ofTerm (SequentialDisjBoth.rebuild (.disj A B) (firstResidue A B X Y Z T) (secondResidue A B X Y Z T)
        (G.cut (z.toHead.right h) (SequentialDisjBoth.fresh
          (G.cut (z.toHead.right h) (firstChild f)) (G.cut (z.toHead.right h) (secondChild g))))).denote :=
  BlockedDisjBoth.source_equation f g h z
end

section
open BlockedDisjBoth SequentialDisjBoth
example {P : Type u} {A B : NormalForm P} {X Y Z T D E I J : List (NormalForm P)}
    (f : G P ((X++.disj A B::Y)++[A]) D) (g : G P ((Z++.disj A B::T)++[B]) E)
    (h : G P I J) (z : At J (.disj A B))
    (hc : PositionalCut.Clean h z (parent f g) (block A B X Y Z T).keep) :
    PositionalCut.Clean h z f ((BlockedMix.firstTag (.disj A B) X Y).before [A]) ∧
      PositionalCut.rank h z f ((BlockedMix.firstTag (.disj A B) X Y).before [A]) <
        PositionalCut.rank h z (parent f g) (block A B X Y Z T).keep :=
  BlockedDisjBoth.first_descent f g h z hc
end

section
open BlockedDisjBoth SequentialDisjBoth
example {P : Type u} {A B : NormalForm P} {X Y Z T D E I J : List (NormalForm P)}
    (f : G P ((X++.disj A B::Y)++[A]) D) (g : G P ((Z++.disj A B::T)++[B]) E)
    (h : G P I J) (z : At J (.disj A B))
    (hc : PositionalCut.Clean h z (parent f g) (block A B X Y Z T).keep) :
    PositionalCut.Clean h z g ((BlockedMix.firstTag (.disj A B) Z T).before [B]) ∧
      PositionalCut.rank h z g ((BlockedMix.firstTag (.disj A B) Z T).before [B]) <
        PositionalCut.rank h z (parent f g) (block A B X Y Z T).keep :=
  BlockedDisjBoth.second_descent f g h z hc
end

section
open BlockedDisjBoth SequentialDisjBoth
example {P : Type u} {A B : NormalForm P} {X Y Z T D E I J : List (NormalForm P)}
    (f : G P ((X++.disj A B::Y)++[A]) D) (g : G P ((Z++.disj A B::T)++[B]) E)
    (h : G P I J) (z : At J (.disj A B))
    (hc : PositionalCut.Clean h z (parent f g) (block A B X Y Z T).keep)
    (k : G P (((BlockedMix.firstTag (.disj A B) X Y).erase++[A])++I) (D++z.erase))
    (l : G P (((BlockedMix.firstTag (.disj A B) Z T).erase++[B])++I) (E++z.erase))
    (hk : k.CutFree) (ak : k.Atomized) (hl : l.CutFree) (al : l.Atomized) :
    PositionalCut.Clean h z (SequentialDisjBoth.fresh k l) (.here (.disj A B) _) ∧
      PositionalCut.rank h z (SequentialDisjBoth.fresh k l) (.here (.disj A B) _) <
        PositionalCut.rank h z (parent f g) (block A B X Y Z T).keep :=
  BlockedDisjBoth.fresh_clean_and_rank f g h z hc k l hk ak hl al
end

section
open BlockedDisjBoth SequentialDisjBoth
example {P : Type u} {A B : NormalForm P} {X Y Z T D E I J : List (NormalForm P)}
    (f : G P ((X++.disj A B::Y)++[A]) D) (g : G P ((Z++.disj A B::T)++[B]) E)
    (h : G P I J) (z : At J (.disj A B))
    (hc : PositionalCut.Clean h z (BlockedDisjBoth.parent f g) (BlockedDisjBoth.block A B X Y Z T).keep)
    (ih : ∀ {K L M N : List (NormalForm P)} (b : G P K L) (v : At L (.disj A B))
      (d : G P M N) (w : At M (.disj A B)),
      PositionalCut.rank b v d w <
        PositionalCut.rank h z (BlockedDisjBoth.parent f g) (BlockedDisjBoth.block A B X Y Z T).keep →
      PositionalCut.Clean b v d w → PositionalCut.Eliminated b v d w) :
    PositionalCut.Eliminated h z (BlockedDisjBoth.parent f g) (BlockedDisjBoth.block A B X Y Z T).keep :=
  CutCommutation.blockedL_disjunctionBoth_rank_step f g h z hc ih
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

theorem literal_source (l : Literal Nat) (X Y Z T : List (NormalForm Nat)) :
    PositionalCut.Eliminated (G.identityNF (.disj .bot (.lit l))) (.here _ [])
      (BlockedDisjBoth.parent (X:=X) (Y:=Y) (Z:=Z) (T:=T)
        (botTail (X++.disj .bot (.lit l)::Y))
        (topContext ((Z++.disj .bot (.lit l)::T)++[.lit l])))
      (BlockedDisjBoth.block .bot (.lit l) X Y Z T).keep := terminal_eliminated _ _ _
example : PositionalCut.Eliminated (G.identityNF (.disj .bot (.lit (.neg 0)))) (.here _ [])
    (BlockedDisjBoth.parent (X:=[]) (Y:=[]) (Z:=[]) (T:=[]) (botTail [.disj .bot (.lit (.neg 0))])
      (topContext [.disj .bot (.lit (.neg 0)),.lit (.neg 0)]))
    (BlockedDisjBoth.block .bot (.lit (.neg 0)) [] [] [] []).keep := literal_source (.neg 0) [] [] [] []
example : PositionalCut.Eliminated (P:=Empty) (G.identityNF (.disj .bot .top)) (.here _ [])
    (BlockedDisjBoth.parent (X:=[]) (Y:=[]) (Z:=[]) (T:=[]) (botTail [.disj .bot .top])
      (topContext [.disj .bot .top,.top]))
    (BlockedDisjBoth.block .bot .top [] [] [] []).keep := terminal_eliminated _ _ _
example : PositionalCut.Eliminated (P:=Empty) (G.identityNF (.disj .bot .top)) (.here _ [])
    (BlockedDisjBoth.parent (X:=[.disj .bot .top]) (Y:=[.disj .bot .top])
      (Z:=[.disj .bot .top]) (T:=[.disj .bot .top])
      (botTail [.disj .bot .top,.disj .bot .top,.disj .bot .top])
      (topContext [.disj .bot .top,.disj .bot .top,.disj .bot .top,.top]))
    (BlockedDisjBoth.block .bot .top [.disj .bot .top] [.disj .bot .top]
      [.disj .bot .top] [.disj .bot .top]).keep := terminal_eliminated _ _ _
example : ((BlockedDisjBoth.block (.bot : NormalForm Empty) .top [.disj .bot .top] [] [] []).route.get
    (.here (.disj .bot .top) [.disj .bot .top,.disj .bot .top,.disj .bot .top])).index = 0 := by rfl
example (C : NormalForm Empty) :
    (selectedCopies C [[C],[C,C],[C]] []).map At.index = [1,4,6] := by rfl
end BlockedDisjBothChecks

#print axioms DosenPetric.Reduced.Gentzen.SequentialDisjBoth.native_equation

#print axioms DosenPetric.Reduced.Gentzen.SequentialDisjBoth.source_denote

#print axioms DosenPetric.Reduced.Gentzen.BlockedDisjBoth.source_equation

#print axioms DosenPetric.Reduced.Gentzen.BlockedDisjBoth.first_descent

#print axioms DosenPetric.Reduced.Gentzen.BlockedDisjBoth.second_descent

#print axioms DosenPetric.Reduced.Gentzen.BlockedDisjBoth.fresh_clean_and_rank

#print axioms DosenPetric.Reduced.Gentzen.CutCommutation.blockedL_disjunctionBoth_rank_step
