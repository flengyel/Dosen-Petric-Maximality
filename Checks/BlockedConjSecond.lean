module
import DosenPetric
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open DosenPetric DosenPetric.Reduced DosenPetric.Reduced.Gentzen
namespace BlockedConjSecondChecks

section
open SequentialConjSecond
example {P : Type u} {Γ Θ F U I J : List (NormalForm P)} {A B : NormalForm P}
    (f : G P Γ (A::F)) (g : G P Θ (B::.conj A B::U)) (h : G P (.conj A B::I) J) :
    ofTerm (G.cut (parent f g) h).denote =
      ofTerm (rebuild (.conj A B) (G.cut (fresh f (G.cut (child g) h)) h)).denote :=
  SequentialConjSecond.native_equation f g h
end

section
open BlockedConjSecond
example {P : Type u} {A B : NormalForm P} {Γ Θ Z T F : List (NormalForm P)}
    (f : G P Γ (A::F)) (g : G P Θ (B::(Z++.conj A B::T))) :
    parent f g = BlockedSource.right2 (.conj A B) (Γ++Θ) [] (F++Z) T
      ((G.conjR f g).reindex rfl (by simp only [List.nil_append,List.append_assoc])) :=
  BlockedConjSecond.parent_source f g
end

section
open BlockedConjSecond
example {P : Type u} {A B : NormalForm P} {Γ Θ F Z T I J : List (NormalForm P)}
    (f : G P Γ (A::F)) (g : G P Θ (B::(Z++.conj A B::T))) (h : G P I J) (z : At I (.conj A B)) :
    ofTerm (PositionalCut.cut (parent f g) (block A B F Z T).keep h z).denote =
      ofTerm (SequentialConjSecond.routed (.conj A B) (residue A B F Z T)
        (G.cut (SequentialConjSecond.fresh f
          (G.cut (SequentialConjSecond.child (SequentialConjSecond.secondChild (parametric A B Z T) g))
            (z.toHead.left h))) (z.toHead.left h))).denote :=
  BlockedConjSecond.source_equation f g h z
end

section
open BlockedConjSecond
example {P : Type u} {A B : NormalForm P} {Γ Θ F Z T I J : List (NormalForm P)}
    (f : G P Γ (A::F)) (g : G P Θ (B::(Z++.conj A B::T))) (h : G P I J) (z : At I (.conj A B))
    (hc : PositionalCut.Clean (parent f g) (block A B F Z T).keep h z) :
    PositionalCut.Clean g (parametric A B Z T).there h z ∧
      PositionalCut.rank g (parametric A B Z T).there h z <
        PositionalCut.rank (parent f g) (block A B F Z T).keep h z :=
  BlockedConjSecond.original_descent f g h z hc
end

section
open BlockedConjSecond
example {P : Type u} {A B : NormalForm P} {Γ Θ F Z T I J : List (NormalForm P)}
    (f : G P Γ (A::F)) (g : G P Θ (B::(Z++.conj A B::T))) (h : G P I J) (z : At I (.conj A B))
    (hc : PositionalCut.Clean (parent f g) (block A B F Z T).keep h z)
    (k : G P (z.erase++Θ) (J++B::(parametric A B Z T).erase)) (hk : k.CutFree) (ak : k.Atomized) :
    PositionalCut.Clean (SequentialConjSecond.fresh f k) (.here (.conj A B) _) h z ∧
      PositionalCut.rank (SequentialConjSecond.fresh f k) (.here (.conj A B) _) h z <
        PositionalCut.rank (parent f g) (block A B F Z T).keep h z :=
  BlockedConjSecond.fresh_clean_and_rank f g h z hc k hk ak
end

section
open BlockedConjSecond
example {P : Type u} {A B : NormalForm P} {Γ Θ F Z T I J : List (NormalForm P)}
    (f : G P Γ (A::F)) (g : G P Θ (B::(Z++.conj A B::T))) (h : G P I J) (z : At I (.conj A B))
    (hc : PositionalCut.Clean (BlockedConjSecond.parent f g) (BlockedConjSecond.block A B F Z T).keep h z)
    (ih : ∀ {K L M N : List (NormalForm P)} (b : G P K L) (v : At L (.conj A B))
      (d : G P M N) (w : At M (.conj A B)),
      PositionalCut.rank b v d w <
        PositionalCut.rank (BlockedConjSecond.parent f g) (BlockedConjSecond.block A B F Z T).keep h z →
      PositionalCut.Clean b v d w → PositionalCut.Eliminated b v d w) :
    PositionalCut.Eliminated (BlockedConjSecond.parent f g) (BlockedConjSecond.block A B F Z T).keep h z :=
  CutCommutation.blockedR_conjunctionSecond_rank_step f g h z hc ih
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

theorem literal_source (l : Literal Nat) (F Z T : List (NormalForm Nat)) :
    PositionalCut.Eliminated
      (BlockedConjSecond.parent (Γ:=[.bot]) (Θ:=[]) (F:=F) (Z:=Z) (T:=T)
        (botOutput (.lit l::F)) (topTail (Z++.conj (.lit l) .top::T)))
      (BlockedConjSecond.block (.lit l) .top F Z T).keep
      (G.identityNF (.conj (.lit l) .top)) (.here _ []) := initial_eliminated _ _ _
example : PositionalCut.Eliminated
    (BlockedConjSecond.parent (Γ:=[.bot]) (Θ:=[]) (F:=[]) (Z:=[]) (T:=[])
      (botOutput [.lit (.neg 0)]) (topTail [.conj (.lit (.neg 0)) .top]))
    (BlockedConjSecond.block (.lit (.neg 0)) .top [] [] []).keep
    (G.identityNF (.conj (.lit (.neg 0)) .top)) (.here _ []) := literal_source (.neg 0) [] [] []
example : PositionalCut.Eliminated (P:=Empty)
    (BlockedConjSecond.parent (Γ:=[.bot]) (Θ:=[]) (F:=[]) (Z:=[]) (T:=[])
      (botOutput [.bot]) (topTail [.conj .bot .top]))
    (BlockedConjSecond.block .bot .top [] [] []).keep
    (G.identityNF (.conj .bot .top)) (.here _ []) := initial_eliminated _ _ _
example : PositionalCut.Eliminated (P:=Empty)
    (BlockedConjSecond.parent (Γ:=[.bot]) (Θ:=[]) (F:=[.conj .bot .top]) (Z:=[.conj .bot .top]) (T:=[.conj .bot .top])
      (botOutput [.bot,.conj .bot .top]) (topTail [.conj .bot .top,.conj .bot .top,.conj .bot .top]))
    (BlockedConjSecond.block .bot .top [.conj .bot .top] [.conj .bot .top] [.conj .bot .top]).keep
    (G.identityNF (.conj .bot .top)) (.here _ []) := initial_eliminated _ _ _
example : ((BlockedConjSecond.block (.bot : NormalForm Empty) .top [.conj .bot .top] [] []).route.get
    (.there (.here (.conj .bot .top) [.conj .bot .top]))).index = 0 := by rfl
end BlockedConjSecondChecks

#print axioms DosenPetric.Reduced.Gentzen.SequentialConjSecond.native_equation

#print axioms DosenPetric.Reduced.Gentzen.BlockedConjSecond.source_equation

#print axioms DosenPetric.Reduced.Gentzen.BlockedConjSecond.original_descent

#print axioms DosenPetric.Reduced.Gentzen.BlockedConjSecond.fresh_clean_and_rank

#print axioms DosenPetric.Reduced.Gentzen.CutCommutation.blockedR_conjunctionSecond_rank_step
