module

public import DosenPetric.GentzenSourceEntryFrames

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

attribute [local simp] EntryFrame.UniqueOn EntryFrame.UniqueExcept copyOffsets SequentSide.context

theorem BlockedL.premise_frame {Γ Δ : List (NormalForm P)} {g : G P Γ Δ}
    (h : BlockedL g) {C : NormalForm P} (x : At Γ C) (hx : g.LowerContraction .left x)
    {I J : List (NormalForm P)} {t : G P I J} (p : Premise g t) :
    EntryFrame .left C t (fun y => p.parent .left y = some x) := by
  cases h
  all_goals apply EntryFrame.contraction_left _ _ _ _ _ _ ?_ x hx p
  all_goals simp only [EntryFrame.index_reindex_iff]
  all_goals first
    | apply EntryFrame.mix
    | apply EntryFrame.conj_left
    | apply EntryFrame.source_disj_left
    | (unfold BlockedSource.conjLLast; apply EntryFrame.conjunction)
  all_goals simp_all
  all_goals intros
  all_goals omega

theorem BlockedR.premise_frame {Γ Δ : List (NormalForm P)} {g : G P Γ Δ}
    (h : BlockedR g) {C : NormalForm P} (x : At Δ C) (hx : g.LowerContraction .right x)
    {I J : List (NormalForm P)} {t : G P I J} (p : Premise g t) :
    EntryFrame .right C t (fun y => p.parent .right y = some x) := by
  cases h
  all_goals apply EntryFrame.contraction_right _ _ _ _ _ _ ?_ x hx p
  all_goals simp only [EntryFrame.index_reindex_iff]
  all_goals first
    | apply EntryFrame.mix
    | apply EntryFrame.source_disj_right
    | apply EntryFrame.conj_right
    | apply EntryFrame.disjunction
  all_goals simp_all
  all_goals intros
  all_goals omega

theorem ReducibleL.entry_unique {Γ Δ Θ Λ U V : List (NormalForm P)} {C : NormalForm P}
    {f : G P Γ (C::Δ)} {g : G P (C::Θ) Λ} {w : G P U V}
    {a : ProofAddress g w} {x : At U C} (hr : ReducibleL f g a x)
    (z : At U C) (hz : a.ascend .left z = some (.here C Θ)) : z = x :=
  hr.entry_unique_with_frames (fun hb v hv p => hb.premise_frame v hv p) z hz

theorem ReducibleR.entry_unique {Γ Δ Θ Λ U V : List (NormalForm P)} {C : NormalForm P}
    {f : G P Γ (C::Δ)} {g : G P (C::Θ) Λ} {w : G P U V}
    {a : ProofAddress f w} {x : At V C} (hr : ReducibleR f g a x)
    (z : At V C) (hz : a.ascend .right z = some (.here C Δ)) : z = x :=
  hr.entry_unique_with_frames (fun hb v hv p => hb.premise_frame v hv p) z hz

end DosenPetric.Reduced.Gentzen
