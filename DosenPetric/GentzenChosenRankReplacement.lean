module

public import DosenPetric.GentzenRankReplacement
public import DosenPetric.GentzenAtomizedReducibility

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u} {Γ Δ Θ Λ U V : List (NormalForm P)} {C : NormalForm P}
variable {f : G P Γ (C::Δ)} {g : G P (C::Θ) Λ} {w : G P U V}

/-- Decompose the ranks for the supplied replacement and its complete bound.
The choice of replacement belongs to its producer. -/
theorem ReducibleL.rank_replacement_for {a : ProofAddress g w} {x : At U C}
    (hr : ReducibleL f g a x) (h : G P U V) (hh : h.CutFree)
    (hbound : ∀ {I J : List (NormalForm P)} {v : G P I J}
      (b : ProofAddress h v) (y : At I C),
      ReducibleL f (a.replace h) ((a.inserted h).append b) y →
        v.rho .left y < w.rho .left x) :
    ∃ O I : List Nat,
        (EligibleSites.leftRanks f g).Perm (w.rho .left x::O) ∧
        (EligibleSites.leftRanks f (a.replace h)).Perm (I++O) ∧
        (∀ r ∈ I, r < w.rho .left x) := by
  classical
  let old := EligibleSites.left f g
  let new := EligibleSites.left f (a.replace h)
  let p := fun k : List Nat × Nat => decide (a.path.IsPrefix k.1)
  let outside := old.erase (a.path,w.rho .left x)
  let inside := new.filter p
  refine ⟨outside.map Prod.snd,inside.map Prod.snd,?_,?_,?_⟩
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


theorem ReducibleR.rank_replacement_for {a : ProofAddress f w} {x : At V C}
    (hr : ReducibleR f g a x) (h : G P U V) (hh : h.CutFree)
    (hbound : ∀ {I J : List (NormalForm P)} {v : G P I J}
      (b : ProofAddress h v) (y : At J C),
      ReducibleR (a.replace h) g ((a.inserted h).append b) y →
        v.rho .right y < w.rho .right x) :
    ∃ O I : List Nat,
        (EligibleSites.rightRanks f g).Perm (w.rho .right x::O) ∧
        (EligibleSites.rightRanks (a.replace h) g).Perm (I++O) ∧
        (∀ r ∈ I, r < w.rho .right x) := by
  classical
  let old := EligibleSites.right f g
  let new := EligibleSites.right (a.replace h) g
  let p := fun k : List Nat × Nat => decide (a.path.IsPrefix k.1)
  let outside := old.erase (a.path,w.rho .right x)
  let inside := new.filter p
  refine ⟨outside.map Prod.snd,inside.map Prod.snd,?_,?_,?_⟩
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
