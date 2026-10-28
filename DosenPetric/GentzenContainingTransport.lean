module

public import DosenPetric.GentzenFiniteOccurrences

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace ProofAddress
variable {Γ Δ U V I J : List (NormalForm P)}
variable {root root' : G P Γ Δ} {w : G P U V} {v : G P I J}

def castRoot (e : root = root') (a : ProofAddress root w) : ProofAddress root' w := e ▸ a

theorem castRoot_path (e : root = root') (a : ProofAddress root w) :
    (a.castRoot e).path = a.path := by cases e; rfl

theorem castRoot_ascend (e : root = root') (a : ProofAddress root w)
    (s : SequentSide) {C : NormalForm P} (x : Place s U V C) :
    (a.castRoot e).ascend s x = a.ascend s x := by cases e; rfl

/-- The actual containing occurrence after replacement of its typed suffix. -/
def containing (a : ProofAddress root v) (b : ProofAddress v w) (h : G P U V) :
    ProofAddress ((a.append b).replace h) (b.replace h) :=
  (a.inserted (b.replace h)).castRoot (a.replace_append b h).symm

theorem containing_path (a : ProofAddress root v) (b : ProofAddress v w) (h : G P U V) :
    (a.containing b h).path = a.path := by
  rw [containing,castRoot_path,inserted_path]

theorem containing_ascend (a : ProofAddress root v) (b : ProofAddress v w) (h : G P U V)
    (s : SequentSide) {C : NormalForm P} (x : Place s I J C) :
    (a.containing b h).ascend s x = a.ascend s x := by
  rw [containing,castRoot_ascend,ascend_inserted]

theorem ProperContains.prefix {a : ProofAddress root v} {b : ProofAddress root w}
    (hp : a.ProperContains b) : a.path.IsPrefix b.path := by
  obtain ⟨c,_,hc⟩ := hp
  exact ⟨c.path,by rw [← hc,append_path]⟩

theorem proper_of_prefix (a : ProofAddress root v) (b : ProofAddress root w)
    (hp : a.path.IsPrefix b.path) (hl : a.path.length < b.path.length) :
    a.ProperContains b := by
  obtain ⟨c,hc⟩ := a.suffix_of_prefix b hp
  refine ⟨c,?_,hc⟩
  intro hn
  have hh := congrArg (fun d => d.path.length) hc
  rw [append_path,List.length_append,hn] at hh
  simp only [List.length_nil] at hh
  omega

theorem proper_of_prefix_ne (a : ProofAddress root v) (b : ProofAddress root w)
    (hp : a.path.IsPrefix b.path) (hn : a.path ≠ b.path) : a.ProperContains b := by
  apply a.proper_of_prefix b hp
  obtain ⟨zs,hz⟩ := hp
  have hzs : zs ≠ [] := by intro he; exact hn (by simpa only [he,List.append_nil] using hz)
  have hl := congrArg List.length hz
  have hh := List.length_pos_iff.mpr hzs
  rw [List.length_append] at hl
  omega

/-- Every new incomparable occurrence has an old occurrence of the same proof,
with the same path and complete typed ancestry. -/
theorem outside_inverse (a : ProofAddress root w) (h : G P U V)
    (b : ProofAddress (a.replace h) v)
    (hab : ¬ a.path.IsPrefix b.path) (hba : ¬ b.path.IsPrefix a.path) :
    ∃ c : ProofAddress root v, c.path = b.path ∧
      ∀ (s : SequentSide) {C : NormalForm P} (x : Place s I J C),
        c.ascend s x = b.ascend s x := by
  obtain ⟨c,hc,he⟩ := (a.inserted h).outside_of_incomparable b
    (by simpa only [inserted_path,List.IsPrefix] using hab)
    (by simpa only [inserted_path,List.IsPrefix] using hba) w
  have hr : (a.inserted h).replace w = root :=
    (a.replace_inserted h w).trans a.replace_original
  refine ⟨c.castRoot hr,(castRoot_path _ _).trans hc,?_⟩
  intro s C x
  exact (castRoot_ascend _ _ s x).trans (he s x)

end ProofAddress

variable {Γ Δ Θ Λ U V : List (NormalForm P)} {C : NormalForm P}
variable {f : G P Γ (C::Δ)} {g : G P (C::Θ) Λ} {w : G P U V}

/-- No strict containing ancestor of the repaired eligible site becomes eligible:
every tied contraction at such an address retains its blocked shape. -/
theorem ReducibleL.blocked_containing {a : ProofAddress g w} {x : At U C}
    (hr : ReducibleL f g a x) (h : G P U V)
    {I J : List (NormalForm P)} {v : G P I J}
    (b : ProofAddress (a.replace h) v) (y : At I C)
    (hy : (a.replace h).TiedRight (b.traceAt .left y))
    (hp : b.ProperContains (a.inserted h)) : BlockedL v := by
  have hlen := ProofAddress.proper_length hp
  obtain ⟨d,hd,he⟩ := hp
  have hprefix : ∃ ys, b.path++ys = a.path := by
    refine ⟨d.path,?_⟩
    have hh := congrArg ProofAddress.path he
    simpa only [ProofAddress.append_path,ProofAddress.inserted_path] using hh
  obtain ⟨I',J',v',c,e,hce,hc⟩ := a.split_prefix b.path hprefix
  cases hce
  have hep : e.path ≠ [] := by
    intro hn
    rw [ProofAddress.inserted_path,ProofAddress.append_path,hc] at hlen
    simp only [hn,List.append_nil] at hlen
    omega
  let c' := c.containing e h
  have heq := c'.occurrence_eq_of_path b (by rw [ProofAddress.containing_path,hc])
  have hprop : (fun o : ProofOccurrence ((c.append e).replace h) =>
      ∀ z : At o.source C,
        ((c.append e).replace h).TiedRight (o.address.traceAt .left z) → BlockedL o.proof)
      (ProofOccurrence.ofAddress c') := by
    intro z hz
    have ha := c'.cluster_ascend .left (.here C Θ) z hz.1
    dsimp only [c'] at ha
    rw [ProofAddress.containing_ascend] at ha
    have hl := (e.replace_lower_iff hep h .left z).mp hz.2
    have ht : g.TiedRight (c.traceAt .left z) := ⟨(c.cluster_iff_ascend _ _ _).mpr ha,hl⟩
    have hb := hr.2.2.2 c z ht ⟨e,hep,rfl⟩
    exact hb.replace_lower e hep x hr.2.1.2 h
  have hresult := heq ▸ hprop
  exact hresult y hy

/-- No strict containing ancestor of the repaired eligible site becomes eligible:
every tied contraction at such an address retains its blocked shape. -/
theorem ReducibleR.blocked_containing {a : ProofAddress f w} {x : At V C}
    (hr : ReducibleR f g a x) (h : G P U V)
    {I J : List (NormalForm P)} {v : G P I J}
    (b : ProofAddress (a.replace h) v) (y : At J C)
    (hy : (a.replace h).TiedLeft (b.traceAt .right y))
    (hp : b.ProperContains (a.inserted h)) : BlockedR v := by
  have hlen := ProofAddress.proper_length hp
  obtain ⟨d,hd,he⟩ := hp
  have hprefix : ∃ ys, b.path++ys = a.path := by
    refine ⟨d.path,?_⟩
    have hh := congrArg ProofAddress.path he
    simpa only [ProofAddress.append_path,ProofAddress.inserted_path] using hh
  obtain ⟨I',J',v',c,e,hce,hc⟩ := a.split_prefix b.path hprefix
  cases hce
  have hep : e.path ≠ [] := by
    intro hn
    rw [ProofAddress.inserted_path,ProofAddress.append_path,hc] at hlen
    simp only [hn,List.append_nil] at hlen
    omega
  let c' := c.containing e h
  have heq := c'.occurrence_eq_of_path b (by rw [ProofAddress.containing_path,hc])
  have hprop : (fun o : ProofOccurrence ((c.append e).replace h) =>
      ∀ z : At o.target C,
        ((c.append e).replace h).TiedLeft (o.address.traceAt .right z) → BlockedR o.proof)
      (ProofOccurrence.ofAddress c') := by
    intro z hz
    have ha := c'.cluster_ascend .right (.here C Δ) z hz.1
    dsimp only [c'] at ha
    rw [ProofAddress.containing_ascend] at ha
    have hl := (e.replace_lower_iff hep h .right z).mp hz.2
    have ht : f.TiedLeft (c.traceAt .right z) := ⟨(c.cluster_iff_ascend _ _ _).mpr ha,hl⟩
    have hb := hr.2.2.2 c z ht ⟨e,hep,rfl⟩
    exact hb.replace_lower e hep x hr.2.1.2 h
  have hresult := heq ▸ hprop
  exact hresult y hy

end DosenPetric.Reduced.Gentzen
