module

public import DosenPetric.GentzenBlockedReplacement

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u} {C : NormalForm P} {Γ Δ Θ Λ : List (NormalForm P)}
variable {f : G P Γ (C::Δ)} {g : G P (C::Θ) Λ}

/-- An unblocked tied contraction has an eligible unblocked ancestor,
possibly itself. Occurrences are compared by proper path length. -/
theorem exists_reducible_left (ht : G.Topmost f g)
    {U V : List (NormalForm P)} {w : G P U V}
    (a : ProofAddress g w) (x : At U C)
    (hx : g.TiedRight (a.traceAt .left x)) (hu : ¬ BlockedL w) :
    ∃ (I J : List (NormalForm P)) (v : G P I J)
      (b : ProofAddress g v) (y : At I C), ReducibleL f g b y := by
  classical
  suffices hh : ∀ n, ∀ {U V : List (NormalForm P)} {w : G P U V}
      (a : ProofAddress g w) (x : At U C), a.path.length = n →
      g.TiedRight (a.traceAt .left x) → ¬ BlockedL w →
      ∃ (I J : List (NormalForm P)) (v : G P I J)
        (b : ProofAddress g v) (y : At I C), ReducibleL f g b y from
    hh _ a x rfl hx hu
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro U V w a x hn hx hu
    by_cases hc : ∀ {I J : List (NormalForm P)} {v : G P I J}
        (b : ProofAddress g v) (y : At I C),
        g.TiedRight (b.traceAt .left y) → b.ProperContains a → BlockedL v
    · exact ⟨_,_,w,a,x,ht,hx,hu,hc⟩
    · simp only [Classical.not_forall] at hc
      obtain ⟨I,J,v,b,y,hb,hba,hv⟩ := hc
      exact ih b.path.length (by have hh := ProofAddress.proper_length hba; omega)
        b y rfl hb hv

/-- Absence of eligible left sites entails blockedness of every tied contraction. -/
theorem blocked_left_of_no_reducible (ht : G.Topmost f g)
    (hn : ∀ {U V : List (NormalForm P)} {w : G P U V}
      (a : ProofAddress g w) (x : At U C), ¬ ReducibleL f g a x)
    {U V : List (NormalForm P)} {w : G P U V}
    (a : ProofAddress g w) (x : At U C)
    (hx : g.TiedRight (a.traceAt .left x)) : BlockedL w := by
  classical
  apply Classical.byContradiction
  intro hu
  obtain ⟨I,J,v,b,y,hb⟩ := exists_reducible_left ht a x hx hu
  exact hn b y hb

/-- An unblocked tied contraction has an eligible unblocked ancestor,
possibly itself. Occurrences are compared by proper path length. -/
theorem exists_reducible_right (ht : G.Topmost f g)
    {U V : List (NormalForm P)} {w : G P U V}
    (a : ProofAddress f w) (x : At V C)
    (hx : f.TiedLeft (a.traceAt .right x)) (hu : ¬ BlockedR w) :
    ∃ (I J : List (NormalForm P)) (v : G P I J)
      (b : ProofAddress f v) (y : At J C), ReducibleR f g b y := by
  classical
  suffices hh : ∀ n, ∀ {U V : List (NormalForm P)} {w : G P U V}
      (a : ProofAddress f w) (x : At V C), a.path.length = n →
      f.TiedLeft (a.traceAt .right x) → ¬ BlockedR w →
      ∃ (I J : List (NormalForm P)) (v : G P I J)
        (b : ProofAddress f v) (y : At J C), ReducibleR f g b y from
    hh _ a x rfl hx hu
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro U V w a x hn hx hu
    by_cases hc : ∀ {I J : List (NormalForm P)} {v : G P I J}
        (b : ProofAddress f v) (y : At J C),
        f.TiedLeft (b.traceAt .right y) → b.ProperContains a → BlockedR v
    · exact ⟨_,_,w,a,x,ht,hx,hu,hc⟩
    · simp only [Classical.not_forall] at hc
      obtain ⟨I,J,v,b,y,hb,hba,hv⟩ := hc
      exact ih b.path.length (by have hh := ProofAddress.proper_length hba; omega)
        b y rfl hb hv

/-- Absence of eligible right sites entails blockedness of every tied contraction. -/
theorem blocked_right_of_no_reducible (ht : G.Topmost f g)
    (hn : ∀ {U V : List (NormalForm P)} {w : G P U V}
      (a : ProofAddress f w) (x : At V C), ¬ ReducibleR f g a x)
    {U V : List (NormalForm P)} {w : G P U V}
    (a : ProofAddress f w) (x : At V C)
    (hx : f.TiedLeft (a.traceAt .right x)) : BlockedR w := by
  classical
  apply Classical.byContradiction
  intro hu
  obtain ⟨I,J,v,b,y,hb⟩ := exists_reducible_right ht a x hx hu
  exact hn b y hb

end DosenPetric.Reduced.Gentzen
