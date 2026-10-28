module

public import DosenPetric.GentzenOutsidePaths

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

namespace ProofSpine
variable {Γ Δ U V : List (NormalForm P)} {k : G P Γ Δ} {w : G P U V}

theorem lower_through_reindex {Γ' Δ' : List (NormalForm P)}
    (eΓ : Γ = Γ') (eΔ : Δ = Δ') (a : ProofSpine (k.reindex eΓ eΔ) w)
    (h : G P U V) :
    ∃ b : ProofSpine k w,
      a.toAddress.replace h = (b.toAddress.replace h).reindex eΓ eΔ := by
  cases eΓ; cases eΔ
  exact ⟨a,rfl⟩

private theorem through_mix {Θ Λ : List (NormalForm P)}
    (f : G P Γ Δ) (g : G P Θ Λ) (a : ProofSpine (G.mix f g) w)
    (side : SequentSide) {D : NormalForm P} (x : Place side U V D)
    (hw : w.LowerContraction side x) (h : G P U V) :
    ∃ (f' : G P Γ Δ) (g' : G P Θ Λ), a.toAddress.replace h = G.mix f' g' := by
  cases a with
  | root =>
    have hk := (G.lowerContraction_iff_arity _ _ _).mp hw
    cases side <;> simp only [G.sourceArity] at hk <;> (try split at hk) <;> omega
  | down p b =>
    have he := G.branches_complete (⟨_,_,_,p⟩ : Branch _)
    simp only [G.branches,List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with he | he <;> cases he
    all_goals rw [replace_down]
    all_goals exact ⟨_,_,rfl⟩

private theorem through_conjR {Θ Λ : List (NormalForm P)} {A B : NormalForm P}
    (f : G P Γ (A::Δ)) (g : G P Θ (B::Λ)) (a : ProofSpine (G.conjR f g) w)
    (side : SequentSide) {D : NormalForm P} (x : Place side U V D)
    (hw : w.LowerContraction side x) (h : G P U V) :
    ∃ (f' : G P Γ (A::Δ)) (g' : G P Θ (B::Λ)), a.toAddress.replace h = G.conjR f' g' := by
  cases a with
  | root =>
    have hk := (G.lowerContraction_iff_arity _ _ _).mp hw
    cases side <;> simp only [G.sourceArity] at hk <;> (try split at hk) <;> omega
  | down p b =>
    have he := G.branches_complete (⟨_,_,_,p⟩ : Branch _)
    simp only [G.branches,List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with he | he <;> cases he
    all_goals rw [replace_down]
    all_goals exact ⟨_,_,rfl⟩

private theorem through_conjL (Θ : List (NormalForm P)) (A B : NormalForm P)
    (f : G P (Γ++A::B::Θ) Δ) (a : ProofSpine (G.conjL Γ Θ Δ A B f) w)
    (side : SequentSide) {D : NormalForm P} (x : Place side U V D)
    (hw : w.LowerContraction side x) (h : G P U V) :
    ∃ f' : G P (Γ++A::B::Θ) Δ, a.toAddress.replace h = G.conjL Γ Θ Δ A B f' := by
  cases a with
  | root =>
    have hk := (G.lowerContraction_iff_arity _ _ _).mp hw
    cases side <;> simp only [G.sourceArity] at hk <;> (try split at hk) <;> omega
  | down p b =>
    have he := G.branches_complete (⟨_,_,_,p⟩ : Branch _)
    simp only [G.branches,List.mem_cons,List.not_mem_nil,or_false] at he
    cases he
    rw [replace_down]
    exact ⟨_,rfl⟩

private theorem through_disjR (Λ : List (NormalForm P)) (A B : NormalForm P)
    (f : G P Γ (Δ++A::B::Λ)) (a : ProofSpine (G.disjR Γ Δ Λ A B f) w)
    (side : SequentSide) {D : NormalForm P} (x : Place side U V D)
    (hw : w.LowerContraction side x) (h : G P U V) :
    ∃ f' : G P Γ (Δ++A::B::Λ), a.toAddress.replace h = G.disjR Γ Δ Λ A B f' := by
  cases a with
  | root =>
    have hk := (G.lowerContraction_iff_arity _ _ _).mp hw
    cases side <;> simp only [G.sourceArity] at hk <;> (try split at hk) <;> omega
  | down p b =>
    have he := G.branches_complete (⟨_,_,_,p⟩ : Branch _)
    simp only [G.branches,List.mem_cons,List.not_mem_nil,or_false] at he
    cases he
    rw [replace_down]
    exact ⟨_,rfl⟩

private theorem through_exchangeL (X Y Θ : List (NormalForm P))
    (f : G P (Γ++X++Y++Θ) Δ) (a : ProofSpine (G.exchangeL Γ X Y Θ Δ f) w)
    (side : SequentSide) {D : NormalForm P} (x : Place side U V D)
    (hw : w.LowerContraction side x) (h : G P U V) :
    ∃ b : ProofSpine f w,
      a.toAddress.replace h = G.exchangeL Γ X Y Θ Δ (b.toAddress.replace h) := by
  cases a with
  | root =>
    have hk := (G.lowerContraction_iff_arity _ _ _).mp hw
    cases side <;> simp only [G.sourceArity] at hk <;> (try split at hk) <;> omega
  | down p b =>
    have he := G.branches_complete (⟨_,_,_,p⟩ : Branch _)
    simp only [G.branches,List.mem_cons,List.not_mem_nil,or_false] at he
    cases he
    rw [replace_down]
    exact ⟨b,rfl⟩

private theorem through_disjL {Θ Λ : List (NormalForm P)} {A B : NormalForm P}
    (f : G P (A::Γ) Δ) (g : G P (B::Θ) Λ) (a : ProofSpine (G.disjL f g) w)
    (side : SequentSide) {D : NormalForm P} (x : Place side U V D)
    (hw : w.LowerContraction side x) (h : G P U V) :
    (∃ b : ProofSpine f w, a.toAddress.replace h = G.disjL (b.toAddress.replace h) g) ∨
    (∃ b : ProofSpine g w, a.toAddress.replace h = G.disjL f (b.toAddress.replace h)) := by
  cases a with
  | root =>
    have hk := (G.lowerContraction_iff_arity _ _ _).mp hw
    cases side <;> simp only [G.sourceArity] at hk <;> (try split at hk) <;> omega
  | down p b =>
    have he := G.branches_complete (⟨_,_,_,p⟩ : Branch _)
    simp only [G.branches,List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with he | he <;> cases he
    · exact .inl ⟨b,replace_down _ _ _⟩
    · exact .inr ⟨b,replace_down _ _ _⟩

private theorem through_disjLLast {Θ Λ : List (NormalForm P)} {A B : NormalForm P}
    (f : G P (Γ++[A]) Δ) (g : G P (Θ++[B]) Λ)
    (a : ProofSpine (BlockedSource.disjLLast f g) w)
    (side : SequentSide) {D : NormalForm P} (x : Place side U V D)
    (hw : w.LowerContraction side x) (h : G P U V) :
    ∃ (f' : G P (Γ++[A]) Δ) (g' : G P (Θ++[B]) Λ),
      a.toAddress.replace h = BlockedSource.disjLLast f' g' := by
  unfold BlockedSource.disjLLast at a ⊢
  obtain ⟨b,hb⟩ := lower_through_reindex _ _ a h
  rw [hb]
  obtain ⟨c,hc⟩ := through_exchangeL _ _ _ _ b side x hw h
  rw [hc]
  obtain ⟨d,hd⟩ := lower_through_reindex _ _ c h
  rw [hd]
  rcases through_disjL _ _ d side x hw h with ⟨e,he⟩ | ⟨e,he⟩
  all_goals rw [he]
  all_goals obtain ⟨j,hj⟩ := lower_through_reindex _ _ e h
  all_goals rw [hj]
  all_goals obtain ⟨l,hl⟩ := through_exchangeL _ _ _ _ j side x hw h
  all_goals rw [hl]
  all_goals obtain ⟨m,hm⟩ := lower_through_reindex _ _ l h
  all_goals rw [hm]
  all_goals exact ⟨_,_,rfl⟩

theorem blockedL_replace (hb : BlockedL k) (a : ProofSpine k w)
    (hp : a.path ≠ []) {D : NormalForm P} (x : At U D)
    (hw : w.LowerContraction .left x) (h : G P U V) :
    BlockedL (a.toAddress.replace h) := by
  cases hb
  all_goals cases a with
  | root => exact False.elim (hp rfl)
  | down p b =>
    have he := G.branches_complete (⟨_,_,_,p⟩ : Branch _)
    simp only [BlockedSource.left2,BlockedSource.left3,G.branches,
      List.mem_cons,List.not_mem_nil,or_false] at he
    cases he
    rw [replace_down]
    simp only [Premise.rebuild]
    obtain ⟨c,hc⟩ := lower_through_reindex _ _ b h
    rw [hc]
    obtain ⟨d,hd⟩ := lower_through_reindex _ _ c h
    rw [hd]
    first
    | (obtain ⟨f',g',he⟩ := through_mix _ _ d .left x hw h
       rw [he]
       exact BlockedL.gammaMix ..)
    | (obtain ⟨f',g',he⟩ := through_conjR _ _ d .left x hw h
       rw [he]
       exact BlockedL.gammaConj ..)
    | (obtain ⟨f',he⟩ := through_conjL _ _ _ _ d .left x hw h
       rw [he]
       exact BlockedL.conjunction ..)
    | (obtain ⟨f',g',he⟩ := through_disjLLast _ _ d .left x hw h
       rw [he]
       first
       | exact BlockedL.gammaDisj ..
       | exact BlockedL.disjunctionFirst ..
       | exact BlockedL.disjunctionSecond ..
       | exact BlockedL.disjunctionBoth ..)

/-- Proper replacement of a right lower contraction preserves each right blocked envelope. -/
theorem blockedR_replace (hb : BlockedR k) (a : ProofSpine k w)
    (hp : a.path ≠ []) {D : NormalForm P} (x : At V D)
    (hw : w.LowerContraction .right x) (h : G P U V) :
    BlockedR (a.toAddress.replace h) := by
  cases hb
  all_goals cases a with
  | root => exact False.elim (hp rfl)
  | down p b =>
    have he := G.branches_complete (⟨_,_,_,p⟩ : Branch _)
    simp only [BlockedSource.right2,BlockedSource.right3,G.branches,
      List.mem_cons,List.not_mem_nil,or_false] at he
    cases he
    rw [replace_down]
    simp only [Premise.rebuild]
    obtain ⟨c,hc⟩ := lower_through_reindex _ _ b h
    rw [hc]
    first
    | (obtain ⟨f',he⟩ := through_disjR _ _ _ _ c .right x hw h
       rw [he]
       exact BlockedR.disjunction ..)
    | (obtain ⟨d,hd⟩ := lower_through_reindex _ _ c h
       rw [hd]
       first
       | (obtain ⟨f',g',he⟩ := through_mix _ _ d .right x hw h
          rw [he]
          exact BlockedR.gammaMix ..)
       | (obtain ⟨f',g',he⟩ := through_disjLLast _ _ d .right x hw h
          rw [he]
          exact BlockedR.gammaDisj ..)
       | (obtain ⟨f',g',he⟩ := through_conjR _ _ d .right x hw h
          rw [he]
          first
          | exact BlockedR.gammaConj ..
          | exact BlockedR.conjunctionFirst ..
          | exact BlockedR.conjunctionSecond ..
          | exact BlockedR.conjunctionBoth ..))

end ProofSpine

/-- Replacing a proper left lower-contraction occurrence by any same-sequent proof
preserves the containing blocked shape. The contracted formula D is arbitrary. -/
theorem BlockedL.replace_lower {Γ Δ U V : List (NormalForm P)}
    {k : G P Γ Δ} {w : G P U V} (hb : BlockedL k)
    (a : ProofAddress k w) (hp : a.path ≠ []) {D : NormalForm P}
    (x : At U D) (hw : w.LowerContraction .left x) (h : G P U V) :
    BlockedL (a.replace h) := by
  have he := ProofSpine.blockedL_replace hb a.spine
    (by simpa only [ProofAddress.spine_path] using hp) x hw h
  simpa only [ProofAddress.spine_toAddress] using he

/-- The independently typed right-side containing-shape theorem. -/
theorem BlockedR.replace_lower {Γ Δ U V : List (NormalForm P)}
    {k : G P Γ Δ} {w : G P U V} (hb : BlockedR k)
    (a : ProofAddress k w) (hp : a.path ≠ []) {D : NormalForm P}
    (x : At V D) (hw : w.LowerContraction .right x) (h : G P U V) :
    BlockedR (a.replace h) := by
  have he := ProofSpine.blockedR_replace hb a.spine
    (by simpa only [ProofAddress.spine_path] using hp) x hw h
  simpa only [ProofAddress.spine_toAddress] using he

end DosenPetric.Reduced.Gentzen
