module

import DosenPetric

set_option autoImplicit false
universe u
open DosenPetric DosenPetric.Reduced DosenPetric.Reduced.Gentzen

example {P : Type u} {Γ Δ U V : List (NormalForm P)}
    {k : G P Γ Δ} {w : G P U V} (hb : BlockedL k)
    (a : ProofAddress k w) (hp : a.path ≠ []) {D : NormalForm P}
    (x : At U D) (hw : w.LowerContraction .left x) (h : G P U V) :
    BlockedL (a.replace h) := hb.replace_lower a hp x hw h

example {P : Type u} {Γ Δ U V : List (NormalForm P)}
    {k : G P Γ Δ} {w : G P U V} (hb : BlockedR k)
    (a : ProofAddress k w) (hp : a.path ≠ []) {D : NormalForm P}
    (x : At V D) (hw : w.LowerContraction .right x) (h : G P U V) :
    BlockedR (a.replace h) := hb.replace_lower a hp x hw h

example {P : Type u} {C : NormalForm P} {Φ Ξ Ω Ψ : List (NormalForm P)}
    (f : G P Φ (C::Ξ)) (g : G P (C::Ω) Ψ) (ht : G.Topmost f g) :
    ∃ (f' : G P Φ (C::Ξ)) (g' : G P (C::Ω) Ψ),
      G.Topmost f' g' ∧ ofTerm (G.cut f' g').denote = ofTerm (G.cut f g).denote ∧
      (∀ {U V : List (NormalForm P)} {w : G P U V}
        (a : ProofAddress g' w) (x : At U C), g'.TiedRight (a.traceAt .left x) → BlockedL w) ∧
      (∀ {U V : List (NormalForm P)} {w : G P U V}
        (a : ProofAddress f' w) (x : At V C), f'.TiedLeft (a.traceAt .right x) → BlockedR w) :=
  blocked_w f g ht

#check BlockedL.replace_lower
#check BlockedR.replace_lower
#check ReducibleL.outside_iff
#check ReducibleR.outside_iff
#check ReducibleL.rank_replacement
#check ReducibleR.rank_replacement
#check FiniteRank.descent_wf
#check blocked_w
#check AtomizationBlockedBoundary.cutFree_equal_atomized
#print axioms blocked_w
