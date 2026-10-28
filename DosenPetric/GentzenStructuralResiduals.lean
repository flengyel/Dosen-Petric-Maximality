module

public import DosenPetric.GentzenResidualRoutes
public import DosenPetric.GentzenRoutePrograms
public import DosenPetric.GentzenCutStructuralCommutation

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace StructuralProgram
variable {F U : List (NormalForm P)} {C : NormalForm P}

/-- The typed occurrence map already realized by this structural program. -/
def route (p : StructuralProgram P F U) : Route F U := Route.tabulate F U (fun a => p.get a)

theorem route_get (p : StructuralProgram P F U) {E : NormalForm P} (a : At U E) :
    p.route.get a = p.get a := Route.get_tabulate _ a

theorem route_arrow (p : StructuralProgram P F U) (o : Op) :
    p.route.sideArrow o = p.arrow o := by
  apply side_ext o
  intro E a
  rw [Route.sideArrow_get, component, route_get]

/-- Realize the residual route by the existing structural rules. -/
def residual (p : StructuralProgram P F U) (x : At F C) (y : At U C)
    (h : p.route.SingleFiber x y) : StructuralProgram P x.erase y.erase :=
  (p.route.residual x y h).program

theorem residual_square (p : StructuralProgram P F U) (x : At F C) (y : At U C)
    (h : p.route.SingleFiber x y) (o : Op) :
    (side P o).comp (x.toHead.arrow o) (p.arrow o) =
      (side P o).comp ((sideM P o).tensor ((side P o).id C) ((p.residual x y h).arrow o))
        (y.toHead.arrow o) := by
  have he := p.route.residual_square x y h o
  rw [route_arrow] at he
  simpa only [residual, Route.program_arrow] using he

end StructuralProgram
namespace PositionalCut
variable {Γ Δ Θ Λ : List (NormalForm P)} {C : NormalForm P}

/-- Positional denotation with both selected head comparisons made explicit. -/
theorem splice_denote (f : G P Γ Δ) (x : At Δ C) (g : G P Θ Λ) (y : At Θ C) :
    ofTerm (cut f x g y).denote =
      comp (ofTerm (append .conj y.erase Γ).invTerm)
        (comp (splice (comp (ofTerm f.denote) (x.toHead.arrow .disj))
          (comp (y.toHead.arrow .conj) (ofTerm g.denote)))
          (ofTerm (append .disj Λ x.erase).toTerm)) := by
  rw [cut, cut_splice, ExchangeScript.left_denote, ExchangeScript.right_denote]

end PositionalCut
namespace CutCommutation

/-- Commute a structural map through the left premise at its unique selected predecessor. -/
theorem same_right {F U Γ Θ Λ : List (NormalForm P)} {C : NormalForm P}
    (p : StructuralProgram P F U) (x : At F C) (y : At U C)
    (h : p.route.SingleFiber x y) (f : G P Γ U) (g : G P Θ Λ) (z : At Θ C) :
    ofTerm (PositionalCut.cut (p.right f) x g z).denote =
      ofTerm (((p.residual x y h).prefixFixed Λ).right (PositionalCut.cut f y g z)).denote := by
  rw [PositionalCut.splice_denote, StructuralProgram.right_denote,
    StructuralProgram.right_denote, PositionalCut.splice_denote]
  have hs : comp (p.arrow .disj) (x.toHead.arrow .disj) =
      comp (y.toHead.arrow .disj) (tensor .disj (id C) ((p.residual x y h).arrow .disj)) :=
    p.residual_square x y h .disj
  rw [Laws.assoc (ofTerm f.denote), hs, ← Laws.assoc (ofTerm f.denote), Splice.residual]
  have ho : comp (ofTerm (append .disj Λ y.erase).toTerm)
      (((p.residual x y h).prefixFixed Λ).arrow .disj) =
      comp (tensor .disj (id (succ Λ)) ((p.residual x y h).arrow .disj))
        (ofTerm (append .disj Λ x.erase).toTerm) :=
    (p.residual x y h).prefixFixed_split .disj Λ
  simp only [Laws.assoc]
  rw [ho]

/-- The independently typed left-side commutation at a unique selected predecessor. -/
theorem same_left {F U Γ Δ Λ : List (NormalForm P)} {C : NormalForm P}
    (p : StructuralProgram P F U) (x : At F C) (y : At U C)
    (h : p.route.SingleFiber x y) (f : G P Γ Δ) (z : At Δ C) (g : G P U Λ) :
    ofTerm (PositionalCut.cut f z (p.left g) x).denote =
      ofTerm (((p.residual x y h).suffixFixed Γ).left (PositionalCut.cut f z g y)).denote := by
  rw [PositionalCut.splice_denote, StructuralProgram.left_denote,
    StructuralProgram.left_denote, PositionalCut.splice_denote]
  have hs : comp (x.toHead.arrow .conj) (p.arrow .conj) =
      comp (tensor .conj (id C) ((p.residual x y h).arrow .conj)) (y.toHead.arrow .conj) :=
    p.residual_square x y h .conj
  rw [← Laws.assoc (x.toHead.arrow .conj), hs, Laws.assoc, Splice.context]
  have hi : comp (((p.residual x y h).suffixFixed Γ).arrow .conj)
      (ofTerm (append .conj y.erase Γ).invTerm) =
      comp (ofTerm (append .conj x.erase Γ).invTerm)
        (tensor .conj ((p.residual x y h).arrow .conj) (id (ante Γ))) :=
    (p.residual x y h).suffixFixed_split .conj Γ
  simp only [Laws.assoc]
  rw [← Laws.assoc (((p.residual x y h).suffixFixed Γ).arrow .conj), hi, Laws.assoc]

end CutCommutation
end DosenPetric.Reduced.Gentzen
