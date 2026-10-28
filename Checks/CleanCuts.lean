module

import DosenPetric

set_option autoImplicit false
universe u
open DosenPetric DosenPetric.Reduced DosenPetric.Reduced.Gentzen

example {P : Type u} {C : NormalForm P} {Φ Ξ Ω Ψ U V : List (NormalForm P)}
    (f : G P Φ (C::Ξ)) (g : G P (C::Ω) Ψ) (w : G P U V) (x : At U C)
    (hat : w.Atomized) (a : ProofAddress g w) (hr : ReducibleL f g a x) :
    ∃ h : G P U V, h.CutFree ∧ h.Atomized ∧ ofTerm h.denote=ofTerm w.denote ∧
      ∀ {I J : List (NormalForm P)} {v : G P I J} (b : ProofAddress h v) (y : At I C),
        ReducibleL f (a.replace h) ((a.inserted h).append b) y → v.rho .left y < w.rho .left x :=
  reducibility_left_atomized f g w x hat a hr

example {P : Type u} {C : NormalForm P} {Φ Ξ Ω Ψ U V : List (NormalForm P)}
    (f : G P Φ (C::Ξ)) (g : G P (C::Ω) Ψ) (w : G P U V) (x : At V C)
    (hat : w.Atomized) (a : ProofAddress f w) (hr : ReducibleR f g a x) :
    ∃ h : G P U V, h.CutFree ∧ h.Atomized ∧ ofTerm h.denote=ofTerm w.denote ∧
      ∀ {I J : List (NormalForm P)} {v : G P I J} (b : ProofAddress h v) (y : At J C),
        ReducibleR (a.replace h) g ((a.inserted h).append b) y → v.rho .right y < w.rho .right x :=
  reducibility_right_atomized f g w x hat a hr

example {P : Type u} {C : NormalForm P} {Φ Ξ Ω Ψ : List (NormalForm P)}
    (f : G P Φ (C::Ξ)) (g : G P (C::Ω) Ψ) (ht : G.Topmost f g) :
    ∃ (f' : G P Φ (C::Ξ)) (g' : G P (C::Ω) Ψ),
      G.Topmost f' g' ∧ f'.Atomized ∧ g'.Atomized ∧
      ofTerm f'.denote=ofTerm f.denote ∧ ofTerm g'.denote=ofTerm g.denote ∧
      (∀ {U V : List (NormalForm P)} {w : G P U V}
        (a : ProofAddress f' w) (x : At V C), f'.TiedLeft (a.traceAt .right x) → BlockedR w) ∧
      (∀ {U V : List (NormalForm P)} {w : G P U V}
        (a : ProofAddress g' w) (x : At U C), g'.TiedRight (a.traceAt .left x) → BlockedL w) :=
  clean_cut_premises f g ht

example {P : Type u} {C : NormalForm P} {Φ Ξ Ω Ψ : List (NormalForm P)}
    (f : G P Φ (C::Ξ)) (g : G P (C::Ω) Ψ) (ht : G.Topmost f g) :
    ∃ (f' : G P Φ (C::Ξ)) (g' : G P (C::Ω) Ψ),
      G.Topmost f' g' ∧ f'.Atomized ∧ g'.Atomized ∧
      ofTerm (G.cut f' g').denote=ofTerm (G.cut f g).denote ∧
      (∀ {U V : List (NormalForm P)} {w : G P U V}
        (a : ProofAddress g' w) (x : At U C), g'.TiedRight (a.traceAt .left x) → BlockedL w) ∧
      (∀ {U V : List (NormalForm P)} {w : G P U V}
        (a : ProofAddress f' w) (x : At V C), f'.TiedLeft (a.traceAt .right x) → BlockedR w) :=
  clean_cut_normalization f g ht

#check Route.atomic_program
#check Route.atomic_program_arrow
#check ContractionSelection.factor_route_preimage
#check reducibility_left_atomized
#check reducibility_right_atomized
#check blocked_normalization_left_atomized
#check blocked_normalization_right_atomized
#check clean_cut_premises
#check clean_cut_normalization
#check CleanCutChecks.boundary_clean
#check AtomizationBlockedBoundary.cutFree_equal_atomized
#print axioms clean_cut_premises
#print axioms clean_cut_normalization
#check W6.SourceLeft.reduces_atomized
#check W6.TerminalOne.reducesFirst_atomized
#check W6.TerminalOne.reducesSecond_atomized
#check W6.NativeLeft.reduces_atomized
#check W6.HeadRight.reduces_atomized
#check SelectedLogicalReducer.right_atomized
#check RoutingInputReducer.left_atomized
#check RoutingInputReducer.right_atomized
#check OppositeUnaryReducer.left_atomized
#check OppositeUnaryReducer.right_atomized
#check CutBase.identity_identity
#check CutBase.zero_identity
#check CutBase.identity_zero
#check CutBase.zero_zero
#check CutBase.thinned_thinned
#check CutBase.top_thinning
#check CutBase.thinning_bot
#check CutBase.endomorphism_thinning
#check CutBase.thinning_endomorphism

example : ofTerm (G.cut G.topI (G.thinL [] [] [.top] .top (G.topI (P:=Empty)))).denote =
    ofTerm (CutBase.topRepair (G.topI (P:=Empty))).denote := CutBase.top_thinning _

example : ofTerm (G.cut (G.thinR [.bot] [] [] .bot (G.botE (P:=Empty))) G.botE).denote =
    ofTerm (G.botE (P:=Empty)).denote := CutBase.thinning_bot _
