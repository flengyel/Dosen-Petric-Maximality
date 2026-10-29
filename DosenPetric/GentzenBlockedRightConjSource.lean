module

public import DosenPetric.GentzenConjOutputNaturality

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace ExchangeScript

theorem seq_side_arrow {F U K : List (NormalForm P)}
    (p : ExchangeScript P F U) (q : ExchangeScript P U K) (o : Op) :
    (p.seq q).arrow o = (side P o).comp (p.arrow o) (q.arrow o) := rfl

end ExchangeScript
namespace BlockedRightConj

theorem script_conjR {Γ Θ F U K L : List (NormalForm P)} {A B : NormalForm P}
    (a : ExchangeScript P K F) (b : ExchangeScript P L U)
    (f : G P Γ (A::F)) (g : G P Θ (B::U)) :
    comp (ofTerm (G.conjR f g).denote)
      (((a.route.parallel b.route).head (.conj A B)).sideArrow .disj) =
      ofTerm (G.conjR ((a.consFixed A).right f) ((b.consFixed B).right g)).denote := by
  have he := Rules.conjRight_output_nat a.route b.route f.denote g.denote
  apply he.trans
  apply Rules.conjRight_congr
  · rw [ofTerm_comp,ExchangeScript.right_denote,ExchangeScript.consFixed_arrow]
    have hh := Route.head_side .disj A a.route
    rw [ExchangeScript.route_arrow] at hh
    exact congrArg (comp (ofTerm f.denote)) hh
  · rw [ofTerm_comp,ExchangeScript.right_denote,ExchangeScript.consFixed_arrow]
    have hh := Route.head_side .disj B b.route
    rw [ExchangeScript.route_arrow] at hh
    exact congrArg (comp (ofTerm g.denote)) hh

theorem source_denote {K F U Γ Θ : List (NormalForm P)} {A B C : NormalForm P}
    (r : Route K (F++U)) (x : At K C) (a : At F C) (b : At U C)
    (p : Route x.erase a.erase) (q : Route x.erase b.erase)
    (ha : r.firstBlock.get a = x) (hb : r.secondBlock.get b = x)
    (hp : ∀ {V : NormalForm P} (v : At a.erase V),
      r.firstBlock.get (a.retain v) = x.retain (p.get v))
    (hq : ∀ {V : NormalForm P} (v : At b.erase V),
      r.secondBlock.get (b.retain v) = x.retain (q.get v))
    (f : G P Γ (A::F)) (g : G P Θ (B::U)) :
    comp (comp (ofTerm (G.conjR f g).denote) ((r.head (.conj A B)).sideArrow .disj))
      ((At.there (B:=.conj A B) x).toHead.arrow .disj) =
      ofTerm (headParent p q ((a.toHead.consFixed A).right f) ((b.toHead.consFixed B).right g)).denote := by
  have hv := Route.selected_blocks_factor r x a b p q ha hb hp hq
  have he := congrArg (fun s => (s.head (.conj A B)).sideArrow .disj) hv
  rw [← Route.head_compose,← Route.head_compose,Route.compose_side,Route.compose_side] at he
  have hx := Route.head_side .disj (.conj A B) x.toHead.route
  rw [ExchangeScript.route_arrow] at hx
  rw [hx] at he
  dsimp only [side,opposite,category] at he
  rw [headParent,ExchangeScript.right_denote,StructuralProgram.right_denote,Route.program_arrow,
    BinaryLogical.toHead_there_arrow,ExchangeScript.seq_side_arrow,ExchangeScript.consFixed_arrow]
  dsimp only [side,sideM,disjMonoidal,opposite,category]
  simp only [Laws.assoc]
  erw [← Laws.assoc ((r.head (.conj A B)).sideArrow .disj),he]
  simp only [← Laws.assoc]
  rw [script_conjR]

end BlockedRightConj
end DosenPetric.Reduced.Gentzen
