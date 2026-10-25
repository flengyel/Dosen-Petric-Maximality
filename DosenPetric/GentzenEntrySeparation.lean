module

public import DosenPetric.GentzenEntryFrames

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

namespace ProofAddress
variable {Γ Δ U V : List (NormalForm P)} {root : G P Γ Δ} {w : G P U V}
variable (a : ProofAddress root w) (s : SequentSide) {C : NormalForm P}
variable (r : Place s Γ Δ C) (y z : Place s U V C)

/-- Two distinct upper origins at an actual containing contraction. -/
structure EntrySeparation where
  parentSource : List (NormalForm P)
  parentTarget : List (NormalForm P)
  childSource : List (NormalForm P)
  childTarget : List (NormalForm P)
  parent : G P parentSource parentTarget
  child : G P childSource childTarget
  stem : ProofAddress root parent
  step : Premise parent child
  suffix : ProofAddress child w
  middle : Place s parentSource parentTarget C
  first : Place s childSource childTarget C
  second : Place s childSource childTarget C
  distinct : first ≠ second
  factor : (stem.down step).append suffix = a
  origin : stem.ascend s middle = some r
  first_parent : step.parent s first = some middle
  second_parent : step.parent s second = some middle
  first_path : suffix.ascend s y = some first
  second_path : suffix.ascend s z = some second
  lower : parent.LowerContraction s middle

namespace EntrySeparation
variable {a s r y z}
theorem proper (e : EntrySeparation a s r y z) : e.stem.ProperContains a := by
  refine ⟨(ProofAddress.root.down e.step).append e.suffix,?_,?_⟩
  · intro h
    have hl := congrArg List.length h
    simp only [ProofAddress.append_path,ProofAddress.path,List.length_append,
      List.length_cons,List.length_nil] at hl
    omega
  · rw [← ProofAddress.append_assoc]
    exact e.factor

def prepend {Ξ Ω : List (NormalForm P)} {outer : G P Ξ Ω}
    (p : Premise outer root) (t : Place s Ξ Ω C)
    (hp : p.parent s r = some t) (e : EntrySeparation a s r y z) :
    EntrySeparation ((ProofAddress.root.down p).append a) s t y z where
  parentSource := e.parentSource
  parentTarget := e.parentTarget
  childSource := e.childSource
  childTarget := e.childTarget
  parent := e.parent
  child := e.child
  stem := (ProofAddress.root.down p).append e.stem
  step := e.step
  suffix := e.suffix
  middle := e.middle
  first := e.first
  second := e.second
  distinct := e.distinct
  factor := by
    change ((ProofAddress.root.down p).append (e.stem.down e.step)).append e.suffix = _
    rw [ProofAddress.append_assoc,e.factor]
  origin := by
    rw [ProofAddress.ascend_append,e.origin]
    simpa only [Option.bind_some,ProofAddress.ascend,Option.bind_fun_some] using hp
  first_parent := e.first_parent
  second_parent := e.second_parent
  first_path := e.first_path
  second_path := e.second_path
  lower := e.lower
end EntrySeparation
end ProofAddress

namespace ProofSpine
variable {Γ Δ U V : List (NormalForm P)} {root : G P Γ Δ} {w : G P U V}

theorem separation_of_collision (a : ProofSpine root w) (s : SequentSide)
    {C : NormalForm P} (r : Place s Γ Δ C) (y z : Place s U V C)
    (hy : a.toAddress.ascend s y = some r) (hz : a.toAddress.ascend s z = some r)
    (hne : y ≠ z) : Nonempty (ProofAddress.EntrySeparation a.toAddress s r y z) := by
  induction a with
  | root => exact False.elim (hne ((Option.some.inj hy).trans (Option.some.inj hz).symm))
  | @down Γ Δ Θ Λ U V root child w p a ih =>
    rw [toAddress,ProofAddress.ascend_append] at hy hz
    cases h₀ : a.toAddress.ascend s y with
    | none => simp only [h₀,Option.bind_none] at hy; cases hy
    | some u =>
      cases h₁ : a.toAddress.ascend s z with
      | none => simp only [h₁,Option.bind_none] at hz; cases hz
      | some v =>
        have hp : p.parent s u = some r := by simpa only [h₀,Option.bind_some,ProofAddress.ascend,Option.bind_fun_some] using hy
        have hq : p.parent s v = some r := by simpa only [h₁,Option.bind_some,ProofAddress.ascend,Option.bind_fun_some] using hz
        by_cases huv : u = v
        · cases huv
          obtain ⟨e⟩ := ih u y z h₀ h₁ hne
          exact ⟨e.prepend p r hp⟩
        · have hl : root.LowerContraction s r := (p.equal_parent_or_lower s r u v hp hq).resolve_left huv
          exact ⟨⟨Γ,Δ,Θ,Λ,root,child,.root,p,a.toAddress,r,u,v,huv,rfl,rfl,hp,hq,h₀,h₁,hl⟩⟩
end ProofSpine

namespace ProofAddress
variable {Γ Δ U V : List (NormalForm P)} {root : G P Γ Δ} {w : G P U V}
theorem separation_of_collision (a : ProofAddress root w) (s : SequentSide)
    {C : NormalForm P} (r : Place s Γ Δ C) (y z : Place s U V C)
    (hy : a.ascend s y = some r) (hz : a.ascend s z = some r) (hne : y ≠ z) :
    Nonempty (EntrySeparation a s r y z) := by
  rw [← a.spine_toAddress] at hy hz ⊢
  exact a.spine.separation_of_collision s r y z hy hz hne
end ProofAddress

section Left
variable {Γ Δ Θ Λ U V : List (NormalForm P)} {C : NormalForm P}
variable {f : G P Γ (C::Δ)} {g : G P (C::Θ) Λ} {w : G P U V}
variable {a : ProofAddress g w} {x : At U C}

theorem ReducibleL.entry_unique_with_frames (hr : ReducibleL f g a x)
    (frames : ∀ {I J K L : List (NormalForm P)} {q : G P I J} {t : G P K L},
      BlockedL q → ∀ (v : At I C), q.LowerContraction .left v →
      ∀ (p : Premise q t), EntryFrame .left C t (fun u => p.parent .left u = some v))
    (z : At U C) (hz : a.ascend .left z = some (.here C Θ)) : z = x := by
  by_cases he : z = x
  · exact he
  obtain ⟨e⟩ := a.separation_of_collision .left (.here C Θ) z x hz
    (a.cluster_ascend .left (.here C Θ) x hr.2.1.1) he
  have hb : BlockedL e.parent := hr.2.2.2 e.stem e.middle
    ⟨(e.stem.cluster_iff_ascend .left _ _).mpr e.origin,e.lower⟩ e.proper
  have hf := frames hb e.middle e.lower e.step
  exact False.elim (e.distinct (hf.unique_origins e.suffix x hr.2.1.2
    z x e.first e.second e.first_parent e.second_parent e.first_path e.second_path))
end Left

section Right
variable {Γ Δ Θ Λ U V : List (NormalForm P)} {C : NormalForm P}
variable {f : G P Γ (C::Δ)} {g : G P (C::Θ) Λ} {w : G P U V}
variable {a : ProofAddress f w} {x : At V C}

theorem ReducibleR.entry_unique_with_frames (hr : ReducibleR f g a x)
    (frames : ∀ {I J K L : List (NormalForm P)} {q : G P I J} {t : G P K L},
      BlockedR q → ∀ (v : At J C), q.LowerContraction .right v →
      ∀ (p : Premise q t), EntryFrame .right C t (fun u => p.parent .right u = some v))
    (z : At V C) (hz : a.ascend .right z = some (.here C Δ)) : z = x := by
  by_cases he : z = x
  · exact he
  obtain ⟨e⟩ := a.separation_of_collision .right (.here C Δ) z x hz
    (a.cluster_ascend .right (.here C Δ) x hr.2.1.1) he
  have hb : BlockedR e.parent := hr.2.2.2 e.stem e.middle
    ⟨(e.stem.cluster_iff_ascend .right _ _).mpr e.origin,e.lower⟩ e.proper
  have hf := frames hb e.middle e.lower e.step
  exact False.elim (e.distinct (hf.unique_origins e.suffix x hr.2.1.2
    z x e.first e.second e.first_parent e.second_parent e.first_path e.second_path))
end Right

end DosenPetric.Reduced.Gentzen
