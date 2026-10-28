module

public import DosenPetric.GentzenOutsideEligibility
public import DosenPetric.GentzenReducibility

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u} {Γ Δ Θ Λ U V : List (NormalForm P)} {C : NormalForm P}
variable {f : G P Γ (C::Δ)} {g : G P (C::Θ) Λ} {w : G P U V}

theorem ReducibleL.lower_unique {a : ProofAddress g w} {x : At U C}
    (hr : ReducibleL f g a x) (y : At U C) (hy : w.LowerContraction .left y) : y = x :=
  At.index_injective _ _ (w.lowerContraction_index_unique .left y x hy hr.2.1.2)

theorem ReducibleR.lower_unique {a : ProofAddress f w} {x : At V C}
    (hr : ReducibleR f g a x) (y : At V C) (hy : w.LowerContraction .right y) : y = x :=
  At.index_injective _ _ (w.lowerContraction_index_unique .right y x hy hr.2.1.2)

/-- Every new eligible site is inside the actual repair, including its root,
or corresponds to an old incomparable eligible occurrence of the same proof. -/
theorem ReducibleL.new_site {a : ProofAddress g w} {x : At U C}
    (hr : ReducibleL f g a x) (h : G P U V) (hh : h.CutFree)
    {I J : List (NormalForm P)} {v : G P I J}
    (b : ProofAddress (a.replace h) v) (y : At I C)
    (hb : ReducibleL f (a.replace h) b y) :
    (∃ c : ProofAddress h v, (a.inserted h).append c = b) ∨
    (∃ c : ProofAddress g v, c.path = b.path ∧
      ¬ a.path.IsPrefix c.path ∧ ¬ c.path.IsPrefix a.path ∧ ReducibleL f g c y) := by
  by_cases ha : (a.inserted h).path.IsPrefix b.path
  · exact .inl ((a.inserted h).suffix_of_prefix b ha)
  · by_cases hba : b.path.IsPrefix (a.inserted h).path
    · have hn : b.path ≠ (a.inserted h).path := by
        intro he
        exact ha (he ▸ List.prefix_refl b.path)
      obtain ⟨zs,hz⟩ := hba
      have hl : b.path.length < (a.inserted h).path.length := by
        have hh' := congrArg List.length hz
        have hz' : zs ≠ [] := by intro he; exact hn (by simpa only [he,List.append_nil] using hz)
        have hp := List.length_pos_iff.mpr hz'
        rw [List.length_append] at hh'
        omega
      exact False.elim (hb.2.2.1 (hr.blocked_containing h b y hb.2.1 (b.proper_of_prefix _ ⟨zs,hz⟩ hl)))
    · have ha' : ¬ a.path.IsPrefix b.path := by simpa only [ProofAddress.inserted_path] using ha
      have hb' : ¬ b.path.IsPrefix a.path := by simpa only [ProofAddress.inserted_path] using hba
      obtain ⟨c,hcp,hca⟩ := a.outside_inverse h b ha' hb'
      refine .inr ⟨c,hcp,?_,?_,?_⟩
      · simpa only [hcp] using ha'
      · simpa only [hcp] using hb'
      · exact (hr.outside_iff h hh c b hcp.symm
          (fun s _ z => (hca s z).symm) (by simpa only [hcp] using ha') y).mp hb

/-- Every new eligible site is inside the actual repair, including its root,
or corresponds to an old incomparable eligible occurrence of the same proof. -/
theorem ReducibleR.new_site {a : ProofAddress f w} {x : At V C}
    (hr : ReducibleR f g a x) (h : G P U V) (hh : h.CutFree)
    {I J : List (NormalForm P)} {v : G P I J}
    (b : ProofAddress (a.replace h) v) (y : At J C)
    (hb : ReducibleR (a.replace h) g b y) :
    (∃ c : ProofAddress h v, (a.inserted h).append c = b) ∨
    (∃ c : ProofAddress f v, c.path = b.path ∧
      ¬ a.path.IsPrefix c.path ∧ ¬ c.path.IsPrefix a.path ∧ ReducibleR f g c y) := by
  by_cases ha : (a.inserted h).path.IsPrefix b.path
  · exact .inl ((a.inserted h).suffix_of_prefix b ha)
  · by_cases hba : b.path.IsPrefix (a.inserted h).path
    · have hn : b.path ≠ (a.inserted h).path := by
        intro he
        exact ha (he ▸ List.prefix_refl b.path)
      obtain ⟨zs,hz⟩ := hba
      have hl : b.path.length < (a.inserted h).path.length := by
        have hh' := congrArg List.length hz
        have hz' : zs ≠ [] := by intro he; exact hn (by simpa only [he,List.append_nil] using hz)
        have hp := List.length_pos_iff.mpr hz'
        rw [List.length_append] at hh'
        omega
      exact False.elim (hb.2.2.1 (hr.blocked_containing h b y hb.2.1 (b.proper_of_prefix _ ⟨zs,hz⟩ hl)))
    · have ha' : ¬ a.path.IsPrefix b.path := by simpa only [ProofAddress.inserted_path] using ha
      have hb' : ¬ b.path.IsPrefix a.path := by simpa only [ProofAddress.inserted_path] using hba
      obtain ⟨c,hcp,hca⟩ := a.outside_inverse h b ha' hb'
      refine .inr ⟨c,hcp,?_,?_,?_⟩
      · simpa only [hcp] using ha'
      · simpa only [hcp] using hb'
      · exact (hr.outside_iff h hh c b hcp.symm
          (fun s _ z => (hca s z).symm) (by simpa only [hcp] using ha') y).mp hb


/-- Distinct eligible occurrences have incomparable paths. -/
theorem ReducibleL.outside_or_same {a : ProofAddress g w} {x : At U C}
    (hr : ReducibleL f g a x) {I J : List (NormalForm P)} {v : G P I J}
    (b : ProofAddress g v) (y : At I C) (hb : ReducibleL f g b y) :
    a.path = b.path ∨ (¬ a.path.IsPrefix b.path ∧ ¬ b.path.IsPrefix a.path) := by
  by_cases he : a.path = b.path
  · exact .inl he
  · refine .inr ⟨?_,?_⟩
    · intro hp
      exact ReducibleL.incomparable f g hb hr (a.proper_of_prefix_ne b hp he)
    · intro hp
      exact ReducibleL.incomparable f g hr hb (b.proper_of_prefix_ne a hp (Ne.symm he))


/-- Distinct eligible occurrences have incomparable paths. -/
theorem ReducibleR.outside_or_same {a : ProofAddress f w} {x : At V C}
    (hr : ReducibleR f g a x) {I J : List (NormalForm P)} {v : G P I J}
    (b : ProofAddress f v) (y : At J C) (hb : ReducibleR f g b y) :
    a.path = b.path ∨ (¬ a.path.IsPrefix b.path ∧ ¬ b.path.IsPrefix a.path) := by
  by_cases he : a.path = b.path
  · exact .inl he
  · refine .inr ⟨?_,?_⟩
    · intro hp
      exact ReducibleR.incomparable f g hb hr (a.proper_of_prefix_ne b hp he)
    · intro hp
      exact ReducibleR.incomparable f g hr hb (b.proper_of_prefix_ne a hp (Ne.symm he))

end DosenPetric.Reduced.Gentzen
