module
import DosenPetric
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open DosenPetric DosenPetric.Reduced DosenPetric.Reduced.Gentzen
namespace BlockedConjFirstChecks

section
open SequentialConjFirst
example {P : Type u} {Γ Θ F U I J : List (NormalForm P)} {A B : NormalForm P}
    (f : G P Γ (A::.conj A B::F)) (g : G P Θ (B::U)) (h : G P (.conj A B::I) J) :
    ofTerm (G.cut (parent f g) h).denote =
      ofTerm (rebuild (.conj A B) (G.cut (fresh (G.cut (child f) h) g) h)).denote :=
  SequentialConjFirst.native_equation f g h
end

section
open BlockedConjFirst
example {P : Type u} {A B : NormalForm P} {Γ Θ X Y U : List (NormalForm P)}
    (f : G P Γ (A::(X++.conj A B::Y))) (g : G P Θ (B::U)) :
    parent f g = BlockedSource.right2 (.conj A B) (Γ++Θ) [] X (Y++U)
      ((G.conjR f g).reindex rfl (by simp only [List.nil_append,List.append_assoc,List.cons_append])) :=
  BlockedConjFirst.parent_source f g
end

section
open BlockedConjFirst
example {P : Type u} {A B : NormalForm P} {Γ Θ X Y U I J : List (NormalForm P)}
    (f : G P Γ (A::(X++.conj A B::Y))) (g : G P Θ (B::U)) (h : G P I J) (z : At I (.conj A B)) :
    ofTerm (PositionalCut.cut (parent f g) (block A B X Y U).keep h z).denote =
      ofTerm (SequentialConjFirst.routed (.conj A B) (residue A B X Y U)
        (G.cut (SequentialConjFirst.fresh
          (G.cut (SequentialConjFirst.child (SequentialConjFirst.firstChild (parametric A B X Y) f))
            (z.toHead.left h)) g) (z.toHead.left h))).denote :=
  BlockedConjFirst.source_equation f g h z
end

section
open BlockedConjFirst
example {P : Type u} {A B : NormalForm P} {Γ Θ X Y U I J : List (NormalForm P)}
    (f : G P Γ (A::(X++.conj A B::Y))) (g : G P Θ (B::U)) (h : G P I J) (z : At I (.conj A B))
    (hc : PositionalCut.Clean (parent f g) (block A B X Y U).keep h z) :
    PositionalCut.Clean f (parametric A B X Y).there h z ∧
      PositionalCut.rank f (parametric A B X Y).there h z <
        PositionalCut.rank (parent f g) (block A B X Y U).keep h z :=
  BlockedConjFirst.original_descent f g h z hc
end

section
open BlockedConjFirst
example {P : Type u} {A B : NormalForm P} {Γ Θ X Y U I J : List (NormalForm P)}
    (f : G P Γ (A::(X++.conj A B::Y))) (g : G P Θ (B::U)) (h : G P I J) (z : At I (.conj A B))
    (hc : PositionalCut.Clean (parent f g) (block A B X Y U).keep h z)
    (k : G P (z.erase++Γ) (J++A::(parametric A B X Y).erase)) (hk : k.CutFree) (ak : k.Atomized) :
    PositionalCut.Clean (SequentialConjFirst.fresh k g) (.here (.conj A B) _) h z ∧
      PositionalCut.rank (SequentialConjFirst.fresh k g) (.here (.conj A B) _) h z <
        PositionalCut.rank (parent f g) (block A B X Y U).keep h z :=
  BlockedConjFirst.fresh_clean_and_rank f g h z hc k hk ak
end

section
open BlockedConjFirst
example {P : Type u} {A B : NormalForm P} {Γ Θ X Y U I J : List (NormalForm P)}
    (f : G P Γ (A::(X++.conj A B::Y))) (g : G P Θ (B::U)) (h : G P I J) (z : At I (.conj A B))
    (hc : PositionalCut.Clean (BlockedConjFirst.parent f g) (BlockedConjFirst.block A B X Y U).keep h z)
    (ih : ∀ {K L M N : List (NormalForm P)} (b : G P K L) (v : At L (.conj A B))
      (d : G P M N) (w : At M (.conj A B)),
      PositionalCut.rank b v d w <
        PositionalCut.rank (BlockedConjFirst.parent f g) (BlockedConjFirst.block A B X Y U).keep h z →
      PositionalCut.Clean b v d w → PositionalCut.Eliminated b v d w) :
    PositionalCut.Eliminated (BlockedConjFirst.parent f g) (BlockedConjFirst.block A B X Y U).keep h z :=
  CutCommutation.blockedR_conjunctionFirst_rank_step f g h z hc ih
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

theorem literal_source (l : Literal Nat) (X Y U : List (NormalForm Nat)) :
    PositionalCut.Eliminated
      (BlockedConjFirst.parent (Γ:=[.bot]) (Θ:=[]) (X:=X) (Y:=Y) (U:=U)
        (botOutput (.lit l::(X++.conj (.lit l) .top::Y))) (topTail U))
      (BlockedConjFirst.block (.lit l) .top X Y U).keep
      (G.identityNF (.conj (.lit l) .top)) (.here _ []) := initial_eliminated _ _ _
example : PositionalCut.Eliminated
    (BlockedConjFirst.parent (Γ:=[.bot]) (Θ:=[]) (X:=[]) (Y:=[]) (U:=[])
      (botOutput [.lit (.neg 0),.conj (.lit (.neg 0)) .top]) (topTail []))
    (BlockedConjFirst.block (.lit (.neg 0)) .top [] [] []).keep
    (G.identityNF (.conj (.lit (.neg 0)) .top)) (.here _ []) := literal_source (.neg 0) [] [] []
example : PositionalCut.Eliminated (P:=Empty)
    (BlockedConjFirst.parent (Γ:=[.bot]) (Θ:=[]) (X:=[]) (Y:=[]) (U:=[])
      (botOutput [.bot,.conj .bot .top]) (topTail []))
    (BlockedConjFirst.block .bot .top [] [] []).keep
    (G.identityNF (.conj .bot .top)) (.here _ []) := initial_eliminated _ _ _
example : PositionalCut.Eliminated (P:=Empty)
    (BlockedConjFirst.parent (Γ:=[.bot]) (Θ:=[]) (X:=[.conj .bot .top]) (Y:=[.conj .bot .top]) (U:=[.conj .bot .top])
      (botOutput [.bot,.conj .bot .top,.conj .bot .top,.conj .bot .top]) (topTail [.conj .bot .top]))
    (BlockedConjFirst.block .bot .top [.conj .bot .top] [.conj .bot .top] [.conj .bot .top]).keep
    (G.identityNF (.conj .bot .top)) (.here _ []) := initial_eliminated _ _ _
example : ((BlockedConjFirst.block (.bot : NormalForm Empty) .top [] [] [.conj .bot .top]).route.get
    (.there (.there (.here (.conj .bot .top) [])))).index = 1 := by rfl
end BlockedConjFirstChecks

#print axioms DosenPetric.Reduced.Gentzen.SequentialAdapters.right_equation

#print axioms DosenPetric.Reduced.Gentzen.SequentialConjFirst.native_equation

#print axioms DosenPetric.Reduced.Gentzen.BlockedConjFirst.source_equation

#print axioms DosenPetric.Reduced.Gentzen.BlockedConjFirst.original_descent

#print axioms DosenPetric.Reduced.Gentzen.BlockedConjFirst.fresh_clean_and_rank

#print axioms DosenPetric.Reduced.Gentzen.CutCommutation.blockedR_conjunctionFirst_rank_step
