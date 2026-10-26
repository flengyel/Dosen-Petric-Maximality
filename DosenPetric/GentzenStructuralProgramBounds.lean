module

public import DosenPetric.GentzenAnchoredRoutes

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace StructuralProgram
variable {F U : List (NormalForm P)}

theorem consFixed_zero_iff (A : NormalForm P) (p : StructuralProgram P F U)
    (a : At (A::U) A) : ((p.consFixed A).get a).index=0 ↔ a.index=0 := by
  cases a with
  | here=>rw [consFixed_here];rfl
  | there a=>rw [consFixed_there];simp only [At.index];omega
end StructuralProgram

namespace ContractionBound
variable {C : NormalForm P} {k : Nat}

theorem routed_unary_left {F U Δ : List (NormalForm P)} {g : G P F Δ} {f : G P U Δ}
    (p : Premise g f) (hp : ∀ j : Branch g,j=⟨U,Δ,f,p⟩)
    (r : ∀ {A : NormalForm P},At U A→At F A)
    (hr : ∀ {A : NormalForm P} (a : At U A),p.parent .left a=some (r a))
    (reject : ∀ x : At F C,x.index=0→¬g.LowerContraction .left x)
    (h : ContractionBound .left C k f (fun a=>(r a).index=0)) :
    ContractionBound .left C k g (fun a=>a.index=0) := by
  apply unary p hp
  · intro x hx hl;exact False.elim (reject x hx hl)
  · apply h.mono
    rintro y ⟨x,hx,hy⟩
    exact (congrArg At.index (Option.some.inj ((hr y).symm.trans hy))).trans hx

theorem routed_unary_right {F U Δ : List (NormalForm P)} {g : G P Δ F} {f : G P Δ U}
    (p : Premise g f) (hp : ∀ j : Branch g,j=⟨Δ,U,f,p⟩)
    (r : ∀ {A : NormalForm P},At U A→At F A)
    (hr : ∀ {A : NormalForm P} (a : At U A),p.parent .right a=some (r a))
    (reject : ∀ x : At F C,x.index=0→¬g.LowerContraction .right x)
    (h : ContractionBound .right C k f (fun a=>(r a).index=0)) :
    ContractionBound .right C k g (fun a=>a.index=0) := by
  apply unary p hp
  · intro x hx hl;exact False.elim (reject x hx hl)
  · apply h.mono
    rintro y ⟨x,hx,hy⟩
    exact (congrArg At.index (Option.some.inj ((hr y).symm.trans hy))).trans hx
end ContractionBound

namespace StructuralProgram
variable {F U Δ : List (NormalForm P)} {C : NormalForm P} {k : Nat}

/-- No contraction introduced in the fixed tail is eligible on the
head ancestry. All such rules still remain present in the proof. -/
theorem consFixed_boundL (p : StructuralProgram P F U) (f : G P (C::U) Δ)
    (h : ContractionBound .left C k f (fun a=>a.index=0)) :
    ContractionBound .left C k ((p.consFixed C).left f) (fun a=>a.index=0) := by
  induction p with
  | identity=>exact h
  | seq p q ih ih'=>exact ih ((q.consFixed C).left f) (ih' f h)
  | exchange Γ X Y Θ=>
    apply ContractionBound.exchangeL
    apply h.mono
    intro a ha
    exact (consFixed_zero_iff C (.exchange Γ X Y Θ) a).mp ha
  | thin Γ Θ A=>
    apply ContractionBound.routed_unary_left (Premise.thinL (C::Γ) Θ Δ A f)
      (r:=(Route.thin (C::Γ) Θ A).get)
    · intro j;simpa only [G.branches,List.mem_singleton] using G.branches_complete j
    · intro B a;rfl
    · intro x hx hl
      have ha:=(G.lowerContraction_iff_arity _ .left x).mp hl
      simp only [G.sourceArity] at ha
      split at ha <;> omega
    · apply h.mono
      intro a ha
      exact (consFixed_zero_iff C (.thin Γ Θ A) a).mp ha
  | contract A gs Θ hn=>
    cases gs with
    | nil=>change 2≤0 at hn;omega
    | cons H hs=>
      apply ContractionBound.routed_unary_left
        (Premise.contractL A ((C::H)::hs) Θ Δ hn f)
        (r:=(copies A ((C::H)::hs) Θ).get)
      · intro j;simpa only [G.branches,List.mem_singleton] using G.branches_complete j
      · intro B a;rfl
      · intro x hx hl
        have hi:=G.lowerContraction_index_unique
          (G.contractL A ((C::H)::hs) Θ Δ hn f) .left x
          (At.shift (gaps ((C::H)::hs)) (.here A Θ)) hl
          (G.LowerContraction.left A ((C::H)::hs) Θ Δ hn f)
        change x.index=(At.shift (gaps ((C::H)::hs)) (.here A Θ)).index at hi
        simp only [At.index_shift,At.index,gaps,List.length_append,List.length_cons,Nat.add_zero] at hi
        omega
      · apply h.mono
        intro a ha
        exact (consFixed_zero_iff C (.contract A (H::hs) Θ hn) a).mp ha
  | reindex hF hU p ih=>cases hF;cases hU;exact ih f h

theorem consFixed_boundR (p : StructuralProgram P F U) (f : G P Δ (C::U))
    (h : ContractionBound .right C k f (fun a=>a.index=0)) :
    ContractionBound .right C k ((p.consFixed C).right f) (fun a=>a.index=0) := by
  induction p with
  | identity=>exact h
  | seq p q ih ih'=>exact ih ((q.consFixed C).right f) (ih' f h)
  | exchange Γ X Y Θ=>
    apply ContractionBound.exchangeR
    apply h.mono
    intro a ha
    exact (consFixed_zero_iff C (.exchange Γ X Y Θ) a).mp ha
  | thin Γ Θ A=>
    apply ContractionBound.routed_unary_right (Premise.thinR Δ (C::Γ) Θ A f)
      (r:=(Route.thin (C::Γ) Θ A).get)
    · intro j;simpa only [G.branches,List.mem_singleton] using G.branches_complete j
    · intro B a;rfl
    · intro x hx hl
      have ha:=(G.lowerContraction_iff_arity _ .right x).mp hl
      simp only [G.sourceArity] at ha
      split at ha <;> omega
    · apply h.mono
      intro a ha
      exact (consFixed_zero_iff C (.thin Γ Θ A) a).mp ha
  | contract A gs Θ hn=>
    cases gs with
    | nil=>change 2≤0 at hn;omega
    | cons H hs=>
      apply ContractionBound.routed_unary_right
        (Premise.contractR Δ A ((C::H)::hs) Θ hn f)
        (r:=(copies A ((C::H)::hs) Θ).get)
      · intro j;simpa only [G.branches,List.mem_singleton] using G.branches_complete j
      · intro B a;rfl
      · intro x hx hl
        have hi:=G.lowerContraction_index_unique
          (G.contractR Δ A ((C::H)::hs) Θ hn f) .right x
          (At.shift (gaps ((C::H)::hs)) (.here A Θ)) hl
          (G.LowerContraction.right Δ A ((C::H)::hs) Θ hn f)
        change x.index=(At.shift (gaps ((C::H)::hs)) (.here A Θ)).index at hi
        simp only [At.index_shift,At.index,gaps,List.length_append,List.length_cons,Nat.add_zero] at hi
        omega
      · apply h.mono
        intro a ha
        exact (consFixed_zero_iff C (.contract A (H::hs) Θ hn) a).mp ha
  | reindex hF hU p ih=>cases hF;cases hU;exact ih f h
end StructuralProgram
end DosenPetric.Reduced.Gentzen
