module

public import DosenPetric.GentzenContainingTransport

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

private theorem prefix_length_lt {xs ys : List Nat} (hp : xs.IsPrefix ys) (hn : xs ≠ ys) :
    xs.length < ys.length := by
  obtain ⟨zs,hz⟩ := hp
  cases zs with
  | nil => exact False.elim (hn (by simpa only [List.append_nil] using hz))
  | cons z zs =>
    have hh := congrArg List.length hz
    simp only [List.length_append,List.length_cons] at hh
    omega

variable {Γ Δ Θ Λ U V : List (NormalForm P)} {C : NormalForm P}
variable {f : G P Γ (C::Δ)} {g : G P (C::Θ) Λ} {w : G P U V}

/-- Full eligibility, including every proper containing contraction, is
equivalent at corresponding incomparable occurrences. -/
theorem ReducibleL.outside_iff {a : ProofAddress g w} {x : At U C}
    (hr : ReducibleL f g a x) (h : G P U V) (hh : h.CutFree)
    {I J : List (NormalForm P)} {v : G P I J}
    (c : ProofAddress g v) (c' : ProofAddress (a.replace h) v)
    (hcp : c'.path = c.path)
    (hca : ∀ (s : SequentSide) {D : NormalForm P} (z : Place s I J D),
      c'.ascend s z = c.ascend s z)
    (hab : ¬ a.path.IsPrefix c.path)
    (y : At I C) : ReducibleL f (a.replace h) c' y ↔ ReducibleL f g c y := by
  constructor
  · intro hc
    refine ⟨hr.1,⟨?_,hc.2.1.2⟩,hc.2.2.1,?_⟩
    · apply (c.cluster_iff_ascend .left (.here C Θ) y).mpr
      rw [← hca]
      exact c'.cluster_ascend .left (.here C Θ) y hc.2.1.1
    · intro A B k b z hz hp
      by_cases hb : b.path.IsPrefix a.path
      · have hn : b.path ≠ a.path := by
          intro he
          apply hab
          rw [← he]
          exact hp.prefix
        exact hr.2.2.2 b z hz (b.proper_of_prefix a hb (prefix_length_lt hb hn))
      · have ha : ¬ a.path.IsPrefix b.path := fun he => hab (he.trans hp.prefix)
        obtain ⟨b',hbp,hba'⟩ := a.outside_of_incomparable b ha hb h
        have ht : (a.replace h).TiedRight (b'.traceAt .left z) := by
          refine ⟨(b'.cluster_iff_ascend .left (.here C Θ) z).mpr ?_,hz.2⟩
          rw [hba']
          exact b.cluster_ascend .left (.here C Θ) z hz.1
        have hp' : b'.ProperContains c' := b'.proper_of_prefix c'
          (by rw [hbp,hcp]; exact hp.prefix)
          (by rw [hbp,hcp]; exact ProofAddress.proper_length hp)
        exact hc.2.2.2 b' z ht hp'
  · intro hc
    refine ⟨⟨hr.1.1,a.replace_cutFree h hr.1.2 hh⟩,⟨?_,hc.2.1.2⟩,hc.2.2.1,?_⟩
    · apply (c'.cluster_iff_ascend .left (.here C Θ) y).mpr
      rw [hca]
      exact c.cluster_ascend .left (.here C Θ) y hc.2.1.1
    · intro A B k b z hz hp
      by_cases hb : b.path.IsPrefix a.path
      · have hn : b.path ≠ a.path := by
          intro he
          apply hab
          have he' : a.path.IsPrefix c'.path := by rw [← he]; exact hp.prefix
          simpa only [hcp] using he'
        have hp' : b.ProperContains (a.inserted h) := b.proper_of_prefix (a.inserted h)
          (by simpa only [ProofAddress.inserted_path] using hb)
          (by simpa only [ProofAddress.inserted_path] using prefix_length_lt hb hn)
        exact hr.blocked_containing h b z hz hp'
      · have ha : ¬ a.path.IsPrefix b.path := by
          intro he
          apply hab
          simpa only [hcp] using he.trans hp.prefix
        obtain ⟨b',hbp,hba'⟩ := a.outside_inverse h b ha hb
        have ht : g.TiedRight (b'.traceAt .left z) := by
          refine ⟨(b'.cluster_iff_ascend .left (.here C Θ) z).mpr ?_,hz.2⟩
          rw [hba']
          exact b.cluster_ascend .left (.here C Θ) z hz.1
        have hp' : b'.ProperContains c := b'.proper_of_prefix c
          (by rw [hbp,← hcp]; exact hp.prefix)
          (by rw [hbp,← hcp]; exact ProofAddress.proper_length hp)
        exact hc.2.2.2 b' z ht hp'

/-- Full eligibility, including every proper containing contraction, is
equivalent at corresponding incomparable occurrences. -/
theorem ReducibleR.outside_iff {a : ProofAddress f w} {x : At V C}
    (hr : ReducibleR f g a x) (h : G P U V) (hh : h.CutFree)
    {I J : List (NormalForm P)} {v : G P I J}
    (c : ProofAddress f v) (c' : ProofAddress (a.replace h) v)
    (hcp : c'.path = c.path)
    (hca : ∀ (s : SequentSide) {D : NormalForm P} (z : Place s I J D),
      c'.ascend s z = c.ascend s z)
    (hab : ¬ a.path.IsPrefix c.path)
    (y : At J C) : ReducibleR (a.replace h) g c' y ↔ ReducibleR f g c y := by
  constructor
  · intro hc
    refine ⟨hr.1,⟨?_,hc.2.1.2⟩,hc.2.2.1,?_⟩
    · apply (c.cluster_iff_ascend .right (.here C Δ) y).mpr
      rw [← hca]
      exact c'.cluster_ascend .right (.here C Δ) y hc.2.1.1
    · intro A B k b z hz hp
      by_cases hb : b.path.IsPrefix a.path
      · have hn : b.path ≠ a.path := by
          intro he
          apply hab
          rw [← he]
          exact hp.prefix
        exact hr.2.2.2 b z hz (b.proper_of_prefix a hb (prefix_length_lt hb hn))
      · have ha : ¬ a.path.IsPrefix b.path := fun he => hab (he.trans hp.prefix)
        obtain ⟨b',hbp,hba'⟩ := a.outside_of_incomparable b ha hb h
        have ht : (a.replace h).TiedLeft (b'.traceAt .right z) := by
          refine ⟨(b'.cluster_iff_ascend .right (.here C Δ) z).mpr ?_,hz.2⟩
          rw [hba']
          exact b.cluster_ascend .right (.here C Δ) z hz.1
        have hp' : b'.ProperContains c' := b'.proper_of_prefix c'
          (by rw [hbp,hcp]; exact hp.prefix)
          (by rw [hbp,hcp]; exact ProofAddress.proper_length hp)
        exact hc.2.2.2 b' z ht hp'
  · intro hc
    refine ⟨⟨a.replace_cutFree h hr.1.1 hh,hr.1.2⟩,⟨?_,hc.2.1.2⟩,hc.2.2.1,?_⟩
    · apply (c'.cluster_iff_ascend .right (.here C Δ) y).mpr
      rw [hca]
      exact c.cluster_ascend .right (.here C Δ) y hc.2.1.1
    · intro A B k b z hz hp
      by_cases hb : b.path.IsPrefix a.path
      · have hn : b.path ≠ a.path := by
          intro he
          apply hab
          have he' : a.path.IsPrefix c'.path := by rw [← he]; exact hp.prefix
          simpa only [hcp] using he'
        have hp' : b.ProperContains (a.inserted h) := b.proper_of_prefix (a.inserted h)
          (by simpa only [ProofAddress.inserted_path] using hb)
          (by simpa only [ProofAddress.inserted_path] using prefix_length_lt hb hn)
        exact hr.blocked_containing h b z hz hp'
      · have ha : ¬ a.path.IsPrefix b.path := by
          intro he
          apply hab
          simpa only [hcp] using he.trans hp.prefix
        obtain ⟨b',hbp,hba'⟩ := a.outside_inverse h b ha hb
        have ht : f.TiedLeft (b'.traceAt .right z) := by
          refine ⟨(b'.cluster_iff_ascend .right (.here C Δ) z).mpr ?_,hz.2⟩
          rw [hba']
          exact b.cluster_ascend .right (.here C Δ) z hz.1
        have hp' : b'.ProperContains c := b'.proper_of_prefix c
          (by rw [hbp,← hcp]; exact hp.prefix)
          (by rw [hbp,← hcp]; exact ProofAddress.proper_length hp)
        exact hc.2.2.2 b' z ht hp'

end DosenPetric.Reduced.Gentzen
