module

public import DosenPetric.GentzenPureNormalForms

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.HasPureNormalForm
universe u
variable {P : Type u}

theorem route_pre {F U Δ : List (NormalForm P)} (r : Route F U)
    {f : Hom (ante U) (succ Δ)} (hf : HasPureNormalForm f) :
    HasPureNormalForm (comp (r.sideArrow .conj) f) :=
  pre _ hf (fun _ p => PurePort.route_factor .conj r p)

theorem route_post {Γ F U : List (NormalForm P)} (r : Route F U)
    {f : Hom (ante Γ) (succ U)} (hf : HasPureNormalForm f) :
    HasPureNormalForm (comp f (r.sideArrow .disj)) :=
  post hf _ (fun _ p => PurePort.route_factor .disj r p)

theorem program_left {F U Δ : List (NormalForm P)} (p : StructuralProgram P F U)
    (f : G P U Δ) (hf : HasPureNormalForm (ofTerm f.denote)) :
    HasPureNormalForm (ofTerm (p.left f).denote) := by
  rw [StructuralProgram.left_denote]
  have h := route_pre p.route hf
  rw [StructuralProgram.route_arrow] at h
  exact h

theorem program_right {Γ F U : List (NormalForm P)} (p : StructuralProgram P F U)
    (f : G P Γ U) (hf : HasPureNormalForm (ofTerm f.denote)) :
    HasPureNormalForm (ofTerm (p.right f).denote) := by
  rw [StructuralProgram.right_denote]
  have h := route_post p.route hf
  rw [StructuralProgram.route_arrow] at h
  exact h

theorem conjL {F U Δ : List (NormalForm P)} (A B : NormalForm P)
    (f : G P (F ++ A :: B :: U) Δ) (hf : HasPureNormalForm (ofTerm f.denote)) :
    HasPureNormalForm (ofTerm (G.conjL F U Δ A B f).denote) := by
  change HasPureNormalForm (comp (ofTerm (Rules.conjLeft F U A B).toTerm) (ofTerm f.denote))
  rw [conjLeft_compare]
  exact pre (logicalSide .conj F U A B) hf (fun _ p => PurePort.logical_factor .conj F U A B p)

theorem disjR {Γ F U : List (NormalForm P)} (A B : NormalForm P)
    (f : G P Γ (F ++ A :: B :: U)) (hf : HasPureNormalForm (ofTerm f.denote)) :
    HasPureNormalForm (ofTerm (G.disjR Γ F U A B f).denote) := by
  change HasPureNormalForm (comp (ofTerm f.denote) (ofTerm (Rules.disjRight F U A B).toTerm))
  rw [disjRight_compare]
  exact post hf (logicalSide .disj F U A B) (fun _ p => PurePort.logical_factor .disj F U A B p)

theorem mix_equation {Γ Θ Δ Λ : List (NormalForm P)} (f : G P Γ Δ) (g : G P Θ Λ) :
    ofTerm (G.mix f g).denote = Reduced.union
      (comp ((Route.takeSecond Θ Γ).sideArrow .conj)
        (comp (ofTerm f.denote) ((Route.takeSecond Λ Δ).sideArrow .disj)))
      (comp ((Route.takeFirst Θ Γ).sideArrow .conj)
        (comp (ofTerm g.denote) ((Route.takeFirst Λ Δ).sideArrow .disj))) := by
  rw [Route.takeSecond_arrow,Route.takeSecond_arrow,Route.takeFirst_arrow,Route.takeFirst_arrow]
  change ofTerm (G.mix f g).denote = Reduced.union
    (comp (comp (ofTerm (append .conj Θ Γ).invTerm) (snd (ante Θ) (ante Γ)))
      (comp (ofTerm f.denote) (comp (inr (succ Λ) (succ Δ)) (ofTerm (append .disj Λ Δ).toTerm))))
    (comp (comp (ofTerm (append .conj Θ Γ).invTerm) (fst (ante Θ) (ante Γ)))
      (comp (ofTerm g.denote) (comp (inl (succ Λ) (succ Δ)) (ofTerm (append .disj Λ Δ).toTerm))))
  simpa only [Laws.assoc] using MixCalculation.native_mix_union f g

theorem mix {Γ Θ Δ Λ : List (NormalForm P)} (f : G P Γ Δ) (g : G P Θ Λ)
    (hf : HasPureNormalForm (ofTerm f.denote)) (hg : HasPureNormalForm (ofTerm g.denote)) :
    HasPureNormalForm (ofTerm (G.mix f g).denote) := by
  rw [mix_equation]
  exact union
    (route_pre (Route.takeSecond Θ Γ) (route_post (Route.takeSecond Λ Δ) hf))
    (route_pre (Route.takeFirst Θ Γ) (route_post (Route.takeFirst Λ Δ) hg))

end DosenPetric.Reduced.Gentzen.HasPureNormalForm
