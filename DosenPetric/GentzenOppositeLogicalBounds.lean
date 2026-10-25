module

public import DosenPetric.GentzenLeftContractionBounds

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace ContractionBound
variable {C : NormalForm P} {k : Nat}

theorem exchangeL_right (Γ X Y Θ Δ : List (NormalForm P)) (f : G P (Γ++X++Y++Θ) Δ)
    (E : At Δ C→Prop) (h : ContractionBound .right C k f E) :
    ContractionBound .right C k (G.exchangeL Γ X Y Θ Δ f) E := by
  apply unary (Premise.exchangeL Γ X Y Θ Δ f)
  · intro j
    simpa only [G.branches,List.mem_singleton] using G.branches_complete j
  · intro x _ hx
    have ha:=(G.lowerContraction_iff_arity _ .right x).mp hx
    simp only [G.sourceArity] at ha
    omega
  · apply h.mono
    rintro y ⟨x,hx,hp⟩
    change some y=some x at hp
    exact (Option.some.inj hp).symm ▸ hx

theorem disjL_right {Γ Θ F U : List (NormalForm P)} {A B : NormalForm P}
    (f : G P (A::Γ) F) (g : G P (B::Θ) U) (E : Nat→Prop)
    (hf : ContractionBound .right C k f (fun x => E x.index))
    (hg : ContractionBound .right C k g (fun x => E (F.length+x.index))) :
    ContractionBound .right C k (G.disjL f g) (fun x => E x.index) := by
  apply step
  · intro x _ hx
    have ha:=(G.lowerContraction_iff_arity _ .right x).mp hx
    simp only [G.sourceArity] at ha
    omega
  · intro j
    have hj:=G.branches_complete j
    simp only [G.branches,List.mem_cons,List.not_mem_nil,or_false] at hj
    cases hj with
    | inl h =>
      cases h
      apply hf.mono
      rintro y ⟨x,hx,hp⟩
      change some (y.before U)=some x at hp
      cases Option.some.inj hp
      change At F C at y
      change E (y.before U).index at hx
      change E y.index
      simpa only [At.index_before] using hx
    | inr h =>
      cases h
      apply hg.mono
      rintro y ⟨x,hx,hp⟩
      change some (At.shift F y)=some x at hp
      cases Option.some.inj hp
      change At U C at y
      change E (At.shift F y).index at hx
      change E (F.length+y.index)
      simpa only [At.index_shift] using hx
end ContractionBound
namespace UnaryCast
theorem exchangeL_right_bound {C : NormalForm P} {k : Nat} {F U : List (NormalForm P)}
    (Γ X Y Θ : List (NormalForm P)) (hF : Γ++X++Y++Θ=F) (hU : Γ++Y++X++Θ=U)
    (Δ : List (NormalForm P)) (f : G P F Δ) (E : Nat→Prop)
    (h : ContractionBound .right C k f (fun x => E x.index)) :
    ContractionBound .right C k (exchangeL Γ X Y Θ hF hU Δ f) (fun x => E x.index) := by
  unfold exchangeL
  apply ContractionBound.index_reindex
  apply ContractionBound.exchangeL_right
  exact h.index_reindex hF.symm rfl
end UnaryCast
namespace BlockedSource
variable {C : NormalForm P} {k : Nat}

theorem headL_right_bound {F Δ : List (NormalForm P)} (A : NormalForm P)
    (f : G P (F++[A]) Δ) (E : Nat→Prop)
    (h : ContractionBound .right C k f (fun x => E x.index)) :
    ContractionBound .right C k (headL A f) (fun x => E x.index) := by
  unfold headL
  exact UnaryCast.exchangeL_right_bound [] F [A] [] _ _ Δ f E h

theorem tailL_right_bound {F Δ : List (NormalForm P)} (A : NormalForm P)
    (f : G P (A::F) Δ) (E : Nat→Prop)
    (h : ContractionBound .right C k f (fun x => E x.index)) :
    ContractionBound .right C k (tailL A f) (fun x => E x.index) := by
  unfold tailL
  exact UnaryCast.exchangeL_right_bound [] [A] F [] _ _ Δ f E h

theorem native_source_right_bound {Γ Θ F U : List (NormalForm P)} {A B : NormalForm P}
    (f : G P (A::Γ) F) (g : G P (B::Θ) U) (E : Nat→Prop)
    (hf : ContractionBound .right C k f (fun x => E x.index))
    (hg : ContractionBound .right C k g (fun x => E (F.length+x.index))) :
    ContractionBound .right C k (disjLLast (tailL A f) (tailL B g)) (fun x => E x.index) := by
  rw [disjLLast_eq]
  apply tailL_right_bound
  apply ContractionBound.disjL_right _ _ E
  · exact headL_right_bound A _ E (tailL_right_bound A f E hf)
  · exact headL_right_bound B _ (fun i => E (F.length+i)) (tailL_right_bound B g (fun i => E (F.length+i)) hg)
end BlockedSource
end DosenPetric.Reduced.Gentzen
