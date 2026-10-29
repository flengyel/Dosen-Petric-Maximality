module
import DosenPetric
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open DosenPetric DosenPetric.Reduced DosenPetric.Reduced.Gentzen
namespace BlockedConjBothChecks

section
open SequentialConjBoth
example {P : Type u} {Γ Θ D E Y I J : List (NormalForm P)} {A B : NormalForm P}
    (p : Route Y D) (q : Route Y E)
    (f : G P Γ (A::.conj A B::D)) (g : G P Θ (B::.conj A B::E)) (h : G P (.conj A B::I) J) :
    ofTerm (G.cut (parent p q f g) h).denote =
      ofTerm (rebuild (.conj A B) p q
        (G.cut (fresh (G.cut (child A (.conj A B) f) h) (G.cut (child B (.conj A B) g) h)) h)).denote :=
  SequentialConjBoth.native_equation p q f g h
end

section
open BlockedConjBoth
example {P : Type u} {A B : NormalForm P} {Γ Θ X Y Z T : List (NormalForm P)}
    (f : G P Γ (A::(X++.conj A B::Y))) (g : G P Θ (B::(Z++.conj A B::T))) :
    parent f g = BlockedSource.right3 (.conj A B) (Γ++Θ) [] X (Y++Z) T
      ((G.conjR f g).reindex rfl (by simp only [List.nil_append,List.append_assoc,List.cons_append])) :=
  BlockedConjBoth.parent_source f g
end

section
open BlockedConjBoth
example {P : Type u} {A B : NormalForm P} {Γ Θ X Y Z T I J : List (NormalForm P)}
    (f : G P Γ (A::(X++.conj A B::Y))) (g : G P Θ (B::(Z++.conj A B::T)))
    (h : G P I J) (z : At I (.conj A B)) :
    ofTerm (PositionalCut.cut (parent f g) (block A B X Y Z T).keep h z).denote =
      ofTerm (SequentialConjBoth.rebuild (.conj A B) (firstResidue A B X Y Z T) (secondResidue A B X Y Z T)
        (G.cut (SequentialConjBoth.fresh
          (G.cut (SequentialConjBoth.child A (.conj A B)
            (SequentialConjFirst.firstChild (BlockedMix.firstTag (.conj A B) X Y) f)) (z.toHead.left h))
          (G.cut (SequentialConjBoth.child B (.conj A B)
            (SequentialConjSecond.secondChild (BlockedMix.firstTag (.conj A B) Z T) g)) (z.toHead.left h)))
          (z.toHead.left h))).denote :=
  BlockedConjBoth.source_equation f g h z
end

section
open BlockedConjBoth
example {P : Type u} {A B : NormalForm P} {Γ Θ X Y Z T I J : List (NormalForm P)}
    (f : G P Γ (A::(X++.conj A B::Y))) (g : G P Θ (B::(Z++.conj A B::T)))
    (h : G P I J) (z : At I (.conj A B))
    (hc : PositionalCut.Clean (parent f g) (block A B X Y Z T).keep h z) :
    PositionalCut.Clean f (BlockedMix.firstTag (.conj A B) X Y).there h z ∧
      PositionalCut.rank f (BlockedMix.firstTag (.conj A B) X Y).there h z <
        PositionalCut.rank (parent f g) (block A B X Y Z T).keep h z :=
  BlockedConjBoth.first_descent f g h z hc
end

section
open BlockedConjBoth
example {P : Type u} {A B : NormalForm P} {Γ Θ X Y Z T I J : List (NormalForm P)}
    (f : G P Γ (A::(X++.conj A B::Y))) (g : G P Θ (B::(Z++.conj A B::T)))
    (h : G P I J) (z : At I (.conj A B))
    (hc : PositionalCut.Clean (parent f g) (block A B X Y Z T).keep h z) :
    PositionalCut.Clean g (BlockedMix.firstTag (.conj A B) Z T).there h z ∧
      PositionalCut.rank g (BlockedMix.firstTag (.conj A B) Z T).there h z <
        PositionalCut.rank (parent f g) (block A B X Y Z T).keep h z :=
  BlockedConjBoth.second_descent f g h z hc
end

section
open BlockedConjBoth
example {P : Type u} {A B : NormalForm P} {Γ Θ X Y Z T I J : List (NormalForm P)}
    (f : G P Γ (A::(X++.conj A B::Y))) (g : G P Θ (B::(Z++.conj A B::T)))
    (h : G P I J) (z : At I (.conj A B))
    (hc : PositionalCut.Clean (parent f g) (block A B X Y Z T).keep h z)
    (k : G P (z.erase++Γ) (J++A::(BlockedMix.firstTag (.conj A B) X Y).erase))
    (l : G P (z.erase++Θ) (J++B::(BlockedMix.firstTag (.conj A B) Z T).erase))
    (hk : k.CutFree) (ak : k.Atomized) (hl : l.CutFree) (al : l.Atomized) :
    PositionalCut.Clean (SequentialConjBoth.fresh k l) (.here (.conj A B) _) h z ∧
      PositionalCut.rank (SequentialConjBoth.fresh k l) (.here (.conj A B) _) h z <
        PositionalCut.rank (parent f g) (block A B X Y Z T).keep h z :=
  BlockedConjBoth.fresh_clean_and_rank f g h z hc k l hk ak hl al
end

section
open BlockedConjBoth
example {P : Type u} {A B : NormalForm P} {Γ Θ X Y Z T I J : List (NormalForm P)}
    (f : G P Γ (A::(X++.conj A B::Y))) (g : G P Θ (B::(Z++.conj A B::T)))
    (h : G P I J) (z : At I (.conj A B))
    (hc : PositionalCut.Clean (BlockedConjBoth.parent f g) (BlockedConjBoth.block A B X Y Z T).keep h z)
    (ih : ∀ {K L M N : List (NormalForm P)} (b : G P K L) (v : At L (.conj A B))
      (d : G P M N) (w : At M (.conj A B)),
      PositionalCut.rank b v d w <
        PositionalCut.rank (BlockedConjBoth.parent f g) (BlockedConjBoth.block A B X Y Z T).keep h z →
      PositionalCut.Clean b v d w → PositionalCut.Eliminated b v d w) :
    PositionalCut.Eliminated (BlockedConjBoth.parent f g) (BlockedConjBoth.block A B X Y Z T).keep h z :=
  CutCommutation.blockedR_conjunctionBoth_rank_step f g h z hc ih
end

def botOutput {P : Type u} : (D : List (NormalForm P)) → G P [.bot] D
  | [] => G.botE
  | E::D => G.headThinR E (botOutput D)
theorem botOutput_cf {P : Type u} (D : List (NormalForm P)) : (botOutput D).CutFree := by
  induction D with
  | nil => rfl
  | cons E D ih => exact G.headThinR_cutFree E _ ih
theorem botOutput_atomized {P : Type u} (D : List (NormalForm P)) : (botOutput D).Atomized := by
  induction D with
  | nil => trivial
  | cons E D ih => exact G.headThinR_atomized E _ ih

theorem initial_eliminated {P : Type u} {C : NormalForm P} {D J : List (NormalForm P)}
    (f : G P [.bot] D) (x : At D C) (h : G P [C] J) : PositionalCut.Eliminated f x h (.here C []) := by
  refine ⟨botOutput (J++x.erase),botOutput_cf _,botOutput_atomized _,?_⟩
  have he := ((disjDiagonal P).toUnit_unique
    (comp (rightIn .conj .bot) (ofTerm (botOutput (J++x.erase)).denote))).trans
    ((disjDiagonal P).toUnit_unique
      (comp (rightIn .conj .bot) (ofTerm (PositionalCut.cut f x h (.here C [])).denote))).symm
  have hh := congrArg (fun k => comp (rightOut .conj .bot) k) he
  simp only [← Laws.assoc,Laws.rightOut_In,Laws.id_comp] at hh
  exact hh

def topTail {P : Type u} : (U : List (NormalForm P)) → G P [] (.top::U)
  | [] => G.topI
  | E::U => G.thinR [] [.top] U E (topTail U)

theorem literal_source (l : Literal Nat) (X Y Z T : List (NormalForm Nat)) :
    PositionalCut.Eliminated
      (BlockedConjBoth.parent (Γ:=[.bot]) (Θ:=[]) (X:=X) (Y:=Y) (Z:=Z) (T:=T)
        (botOutput (.lit l::(X++.conj (.lit l) .top::Y))) (topTail (Z++.conj (.lit l) .top::T)))
      (BlockedConjBoth.block (.lit l) .top X Y Z T).keep
      (G.identityNF (.conj (.lit l) .top)) (.here _ []) := initial_eliminated _ _ _
example : PositionalCut.Eliminated
    (BlockedConjBoth.parent (Γ:=[.bot]) (Θ:=[]) (X:=[]) (Y:=[]) (Z:=[]) (T:=[])
      (botOutput [.lit (.neg 0),.conj (.lit (.neg 0)) .top]) (topTail [.conj (.lit (.neg 0)) .top]))
    (BlockedConjBoth.block (.lit (.neg 0)) .top [] [] [] []).keep
    (G.identityNF (.conj (.lit (.neg 0)) .top)) (.here _ []) := literal_source (.neg 0) [] [] [] []
example : PositionalCut.Eliminated (P:=Empty)
    (BlockedConjBoth.parent (Γ:=[.bot]) (Θ:=[]) (X:=[]) (Y:=[]) (Z:=[]) (T:=[])
      (botOutput [.bot,.conj .bot .top]) (topTail [.conj .bot .top]))
    (BlockedConjBoth.block .bot .top [] [] [] []).keep
    (G.identityNF (.conj .bot .top)) (.here _ []) := initial_eliminated _ _ _
example : PositionalCut.Eliminated (P:=Empty)
    (BlockedConjBoth.parent (Γ:=[.bot]) (Θ:=[]) (X:=[.conj .bot .top]) (Y:=[.conj .bot .top])
      (Z:=[.conj .bot .top]) (T:=[.conj .bot .top])
      (botOutput [.bot,.conj .bot .top,.conj .bot .top,.conj .bot .top])
      (topTail [.conj .bot .top,.conj .bot .top,.conj .bot .top]))
    (BlockedConjBoth.block .bot .top [.conj .bot .top] [.conj .bot .top] [.conj .bot .top] [.conj .bot .top]).keep
    (G.identityNF (.conj .bot .top)) (.here _ []) := initial_eliminated _ _ _
example : ((BlockedConjBoth.block (.bot : NormalForm Empty) .top [.conj .bot .top] [] [] []).route.get
    (.there (.here (.conj .bot .top) [.conj .bot .top,.conj .bot .top]))).index = 0 := by rfl
example (C : NormalForm Empty) : (selectedCopies C [[],[C],[C,C]] [C]).map At.index = [0,2,5] := by rfl
end BlockedConjBothChecks

#print axioms DosenPetric.Reduced.Gentzen.SequentialConjBoth.native_equation

#print axioms DosenPetric.Reduced.Gentzen.SequentialConjBoth.source_denote

#print axioms DosenPetric.Reduced.Gentzen.BlockedConjBoth.source_equation

#print axioms DosenPetric.Reduced.Gentzen.BlockedConjBoth.first_descent

#print axioms DosenPetric.Reduced.Gentzen.BlockedConjBoth.second_descent

#print axioms DosenPetric.Reduced.Gentzen.BlockedConjBoth.fresh_clean_and_rank

#print axioms DosenPetric.Reduced.Gentzen.CutCommutation.blockedR_conjunctionBoth_rank_step
