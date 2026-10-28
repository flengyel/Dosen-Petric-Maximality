module

public import DosenPetric.GentzenEligibleEnumeration
public import DosenPetric.FiniteRankDescent

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u} {Γ Δ Θ Λ U V : List (NormalForm P)} {C : NormalForm P}
variable {f : G P Γ (C::Δ)} {g : G P (C::Θ) Λ} {w : G P U V}

namespace EligibleSites

noncomputable def leftRanks (f : G P Γ (C::Δ)) (g : G P (C::Θ) Λ) : List Nat :=
  (left f g).map Prod.snd

noncomputable def rightRanks (f : G P Γ (C::Δ)) (g : G P (C::Θ) Λ) : List Nat :=
  (right f g).map Prod.snd

end EligibleSites

theorem ReducibleL.outside_keys {a : ProofAddress g w} {x : At U C}
    (hr : ReducibleL f g a x) (h : G P U V) (hh : h.CutFree) :
    ((EligibleSites.left f (a.replace h)).filter
      (fun k => !decide (a.path.IsPrefix k.1))).Perm
    ((EligibleSites.left f g).erase (a.path,w.rho .left x)) := by
  classical
  have hs : (a.path,w.rho .left x) ∈ EligibleSites.left f g :=
    (EligibleSites.mem_left f g _).mpr ⟨ProofOccurrence.ofAddress a,x,hr,rfl⟩
  apply (List.perm_ext_iff_of_nodup
    ((EligibleSites.left_nodup f (a.replace h)).filter _)
    ((EligibleSites.left_nodup f g).erase _)).mpr
  intro k
  constructor
  · intro hk
    obtain ⟨hk,hnot⟩ := List.mem_filter.mp hk
    have hn : ¬ a.path.IsPrefix k.1 := by simpa using hnot
    obtain ⟨o,y,ho,hk⟩ := (EligibleSites.mem_left f (a.replace h) k).mp hk
    rcases hr.new_site h hh o.address y ho with ⟨b,hb⟩ | ⟨b,hbp,hba,hab,hbr⟩
    · apply False.elim
      apply hn
      rw [hk]
      exact ⟨b.path,by rw [← hb,ProofAddress.append_path,ProofAddress.inserted_path]⟩
    · apply (EligibleSites.left_nodup f g).mem_erase_iff.mpr
      refine ⟨?_,(EligibleSites.mem_left f g k).mpr
        ⟨ProofOccurrence.ofAddress b,y,hbr,by simpa only [ProofOccurrence.ofAddress,hbp] using hk⟩⟩
      intro he
      apply hn
      rw [he]
      exact List.prefix_refl _
  · intro hk
    obtain ⟨hne,hk⟩ := (EligibleSites.left_nodup f g).mem_erase_iff.mp hk
    have hkey := hk
    obtain ⟨o,y,ho,hk⟩ := (EligibleSites.mem_left f g k).mp hk
    have hp : a.path ≠ o.address.path := by
      intro he
      apply hne
      exact EligibleSites.left_path_unique f g hkey hs (by rw [hk]; exact he.symm)
    have hout := hr.outside_or_same o.address y ho
    rcases hout with he | ⟨ha,hb⟩
    · exact False.elim (hp he)
    · obtain ⟨b,hbp,hba⟩ := a.outside_of_incomparable o.address ha hb h
      have hbr := (hr.outside_iff h hh o.address b hbp hba ha y).mpr ho
      apply List.mem_filter.mpr
      refine ⟨(EligibleSites.mem_left f (a.replace h) k).mpr
        ⟨ProofOccurrence.ofAddress b,y,hbr,by simpa only [ProofOccurrence.ofAddress,hbp] using hk⟩,?_⟩
      have hn : ¬ a.path.IsPrefix k.1 := by rw [hk]; exact ha
      simpa using hn

/-- A completed local repair replaces exactly one eligible rank by finitely
many smaller ranks; all incomparable rank multiplicities are retained. -/
theorem ReducibleL.rank_replacement {a : ProofAddress g w} {x : At U C}
    (hr : ReducibleL f g a x) :
    ∃ h : G P U V, h.CutFree ∧ ofTerm h.denote = ofTerm w.denote ∧
      ∃ O I : List Nat,
        (EligibleSites.leftRanks f g).Perm (w.rho .left x::O) ∧
        (EligibleSites.leftRanks f (a.replace h)).Perm (I++O) ∧
        (∀ r ∈ I, r < w.rho .left x) := by
  classical
  obtain ⟨h,hh,he,hbound⟩ := reducibility_left f g w x a hr
  let old := EligibleSites.left f g
  let new := EligibleSites.left f (a.replace h)
  let p := fun k : List Nat × Nat => decide (a.path.IsPrefix k.1)
  let outside := old.erase (a.path,w.rho .left x)
  let inside := new.filter p
  refine ⟨h,hh,he,outside.map Prod.snd,inside.map Prod.snd,?_,?_,?_⟩
  · have hs : (a.path,w.rho .left x) ∈ old :=
      (EligibleSites.mem_left f g _).mpr ⟨ProofOccurrence.ofAddress a,x,hr,rfl⟩
    exact (List.perm_cons_erase hs).map Prod.snd
  · have hsplit := (List.filter_append_perm p new).symm.map Prod.snd
    simp only [List.map_append] at hsplit
    exact hsplit.trans (List.Perm.append (List.Perm.refl _)
      ((hr.outside_keys h hh).map Prod.snd))
  · intro r hrank
    obtain ⟨k,hk,hkr⟩ := List.mem_map.mp hrank
    obtain ⟨hk,hp⟩ := List.mem_filter.mp hk
    have hprefix : a.path.IsPrefix k.1 := by simpa only [p,decide_eq_true_eq] using hp
    obtain ⟨o,y,ho,hkey⟩ := (EligibleSites.mem_left f (a.replace h) k).mp hk
    obtain ⟨b,hb⟩ := (a.inserted h).suffix_of_prefix o.address
      (by simpa only [ProofAddress.inserted_path,hkey,List.IsPrefix] using hprefix)
    have hsmall := hbound b y (by rw [hb]; exact ho)
    rw [hkey] at hkr
    exact hkr ▸ hsmall

theorem ReducibleR.outside_keys {a : ProofAddress f w} {x : At V C}
    (hr : ReducibleR f g a x) (h : G P U V) (hh : h.CutFree) :
    ((EligibleSites.right (a.replace h) g).filter
      (fun k => !decide (a.path.IsPrefix k.1))).Perm
    ((EligibleSites.right f g).erase (a.path,w.rho .right x)) := by
  classical
  have hs : (a.path,w.rho .right x) ∈ EligibleSites.right f g :=
    (EligibleSites.mem_right f g _).mpr ⟨ProofOccurrence.ofAddress a,x,hr,rfl⟩
  apply (List.perm_ext_iff_of_nodup
    ((EligibleSites.right_nodup (a.replace h) g).filter _)
    ((EligibleSites.right_nodup f g).erase _)).mpr
  intro k
  constructor
  · intro hk
    obtain ⟨hk,hnot⟩ := List.mem_filter.mp hk
    have hn : ¬ a.path.IsPrefix k.1 := by simpa using hnot
    obtain ⟨o,y,ho,hk⟩ := (EligibleSites.mem_right (a.replace h) g k).mp hk
    rcases hr.new_site h hh o.address y ho with ⟨b,hb⟩ | ⟨b,hbp,hba,hab,hbr⟩
    · apply False.elim
      apply hn
      rw [hk]
      exact ⟨b.path,by rw [← hb,ProofAddress.append_path,ProofAddress.inserted_path]⟩
    · apply (EligibleSites.right_nodup f g).mem_erase_iff.mpr
      refine ⟨?_,(EligibleSites.mem_right f g k).mpr
        ⟨ProofOccurrence.ofAddress b,y,hbr,by simpa only [ProofOccurrence.ofAddress,hbp] using hk⟩⟩
      intro he
      apply hn
      rw [he]
      exact List.prefix_refl _
  · intro hk
    obtain ⟨hne,hk⟩ := (EligibleSites.right_nodup f g).mem_erase_iff.mp hk
    have hkey := hk
    obtain ⟨o,y,ho,hk⟩ := (EligibleSites.mem_right f g k).mp hk
    have hp : a.path ≠ o.address.path := by
      intro he
      apply hne
      exact EligibleSites.right_path_unique f g hkey hs (by rw [hk]; exact he.symm)
    have hout := hr.outside_or_same o.address y ho
    rcases hout with he | ⟨ha,hb⟩
    · exact False.elim (hp he)
    · obtain ⟨b,hbp,hba⟩ := a.outside_of_incomparable o.address ha hb h
      have hbr := (hr.outside_iff h hh o.address b hbp hba ha y).mpr ho
      apply List.mem_filter.mpr
      refine ⟨(EligibleSites.mem_right (a.replace h) g k).mpr
        ⟨ProofOccurrence.ofAddress b,y,hbr,by simpa only [ProofOccurrence.ofAddress,hbp] using hk⟩,?_⟩
      have hn : ¬ a.path.IsPrefix k.1 := by rw [hk]; exact ha
      simpa using hn

/-- A completed local repair replaces exactly one eligible rank by finitely
many smaller ranks; all incomparable rank multiplicities are retained. -/
theorem ReducibleR.rank_replacement {a : ProofAddress f w} {x : At V C}
    (hr : ReducibleR f g a x) :
    ∃ h : G P U V, h.CutFree ∧ ofTerm h.denote = ofTerm w.denote ∧
      ∃ O I : List Nat,
        (EligibleSites.rightRanks f g).Perm (w.rho .right x::O) ∧
        (EligibleSites.rightRanks (a.replace h) g).Perm (I++O) ∧
        (∀ r ∈ I, r < w.rho .right x) := by
  classical
  obtain ⟨h,hh,he,hbound⟩ := reducibility_right f g w x a hr
  let old := EligibleSites.right f g
  let new := EligibleSites.right (a.replace h) g
  let p := fun k : List Nat × Nat => decide (a.path.IsPrefix k.1)
  let outside := old.erase (a.path,w.rho .right x)
  let inside := new.filter p
  refine ⟨h,hh,he,outside.map Prod.snd,inside.map Prod.snd,?_,?_,?_⟩
  · have hs : (a.path,w.rho .right x) ∈ old :=
      (EligibleSites.mem_right f g _).mpr ⟨ProofOccurrence.ofAddress a,x,hr,rfl⟩
    exact (List.perm_cons_erase hs).map Prod.snd
  · have hsplit := (List.filter_append_perm p new).symm.map Prod.snd
    simp only [List.map_append] at hsplit
    exact hsplit.trans (List.Perm.append (List.Perm.refl _)
      ((hr.outside_keys h hh).map Prod.snd))
  · intro r hrank
    obtain ⟨k,hk,hkr⟩ := List.mem_map.mp hrank
    obtain ⟨hk,hp⟩ := List.mem_filter.mp hk
    have hprefix : a.path.IsPrefix k.1 := by simpa only [p,decide_eq_true_eq] using hp
    obtain ⟨o,y,ho,hkey⟩ := (EligibleSites.mem_right (a.replace h) g k).mp hk
    obtain ⟨b,hb⟩ := (a.inserted h).suffix_of_prefix o.address
      (by simpa only [ProofAddress.inserted_path,hkey,List.IsPrefix] using hprefix)
    have hsmall := hbound b y (by rw [hb]; exact ho)
    rw [hkey] at hkr
    exact hkr ▸ hsmall

end DosenPetric.Reduced.Gentzen
