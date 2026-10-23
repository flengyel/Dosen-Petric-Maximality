module

public import DosenPetric.GentzenDisjointRanks

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.W1.DisjointContraction
universe u
variable {P : Type u}

/-- Proved output package; no law below is a construction hypothesis. -/
structure LeftLaws (d : Disjoint.Data P) (hn : 2 ≤ d.outer0.length) (hm : 2 ≤ d.es.length)
    (Δ : List (NormalForm P)) (f : G P d.F Δ) : Prop where
  denote : ofTerm (newL d hn hm Δ f).denote = ofTerm (oldL d hn hm Δ f).denote
  countOld : (oldL d hn hm Δ f).cutCount = f.cutCount
  countNew : (newL d hn hm Δ f).cutCount = f.cutCount
  cutFree : (newL d hn hm Δ f).CutFree ↔ (oldL d hn hm Δ f).CutFree
  atomized : (newL d hn hm Δ f).Atomized ↔ (oldL d hn hm Δ f).Atomized
  oldAtomized : (oldL d hn hm Δ f).Atomized ↔ f.Atomized
  newAtomized : (newL d hn hm Δ f).Atomized ↔ f.Atomized
  relation : (newL d hn hm Δ f).relation = (oldL d hn hm Δ f).relation
  oldC : (oldL d hn hm Δ f).rho .left d.xC = LCL d hn Δ f+d.outer0.length
  newC : (newL d hn hm Δ f).rho .left d.xC = LCL d hn Δ f+1
  oldE : (oldL d hn hm Δ f).rho .left d.xE = LEL d hm Δ f+1
  newE : (newL d hn hm Δ f).rho .left d.xE = LEL d hm Δ f+d.es.length
  Cdecreases : (newL d hn hm Δ f).rho .left d.xC < (oldL d hn hm Δ f).rho .left d.xC
  Eincreases : (oldL d hn hm Δ f).rho .left d.xE < (newL d hn hm Δ f).rho .left d.xE
  sumBalance : endpointSumL d Δ (oldL d hn hm Δ f)+d.es.length =
    endpointSumL d Δ (newL d hn hm Δ f)+d.outer0.length
  otherOld : ∀ {A : NormalForm P} (z : At d.K A) (hc : z.index ≠ d.xC.index) (he : z.index ≠ d.xE.index),
    (oldL d hn hm Δ f).rho .left z = 2+f.rho .left (d.originalViaE z hc he)
  otherNew : ∀ {A : NormalForm P} (z : At d.K A) (hc : z.index ≠ d.xC.index) (he : z.index ≠ d.xE.index),
    (newL d hn hm Δ f).rho .left z = 2+f.rho .left (d.originalViaE z hc he)

theorem leftLaws (d : Disjoint.Data P) (hn : 2 ≤ d.outer0.length) (hm : 2 ≤ d.es.length)
    (Δ : List (NormalForm P)) (f : G P d.F Δ) : LeftLaws d hn hm Δ f :=
  ⟨denoteL ..,oldL_count ..,newL_count ..,cutFreeL ..,atomizedL ..,
    oldL_atomized ..,newL_atomized ..,relationL ..,old_xCL ..,new_xCL ..,
    old_xEL ..,new_xEL ..,C_decreasesL ..,E_increasesL ..,sum_balanceL ..,
    (fun z hc he => other_oldL d hn hm Δ f z hc he),
    (fun z hc he => other_newL d hn hm Δ f z hc he)⟩

theorem fixedGap_left (C E : NormalForm P) (pre post hs : List (List (NormalForm P)))
    (H U V Θ Δ : List (NormalForm P))
    (hn : 2 ≤ (pre++(U++(repeated E (H::hs)++V))::post).length) (hm : 2 ≤ (H::hs).length)
    (f : G P ((repeated C pre++U)++repeated E (H::hs)++(V++C::(repeated C post++Θ))) Δ) :
    LeftLaws (Disjoint.fixedGap C E pre post hs H U V Θ) hn hm Δ f := leftLaws ..

/-- Proved output package; no law below is a construction hypothesis. -/
structure RightLaws (d : Disjoint.Data P) (hn : 2 ≤ d.outer0.length) (hm : 2 ≤ d.es.length)
    (Γ : List (NormalForm P)) (f : G P Γ d.F) : Prop where
  denote : ofTerm (newR d hn hm Γ f).denote = ofTerm (oldR d hn hm Γ f).denote
  countOld : (oldR d hn hm Γ f).cutCount = f.cutCount
  countNew : (newR d hn hm Γ f).cutCount = f.cutCount
  cutFree : (newR d hn hm Γ f).CutFree ↔ (oldR d hn hm Γ f).CutFree
  atomized : (newR d hn hm Γ f).Atomized ↔ (oldR d hn hm Γ f).Atomized
  oldAtomized : (oldR d hn hm Γ f).Atomized ↔ f.Atomized
  newAtomized : (newR d hn hm Γ f).Atomized ↔ f.Atomized
  relation : (newR d hn hm Γ f).relation = (oldR d hn hm Γ f).relation
  oldC : (oldR d hn hm Γ f).rho .right d.xC = LCR d hn Γ f+d.outer0.length
  newC : (newR d hn hm Γ f).rho .right d.xC = LCR d hn Γ f+1
  oldE : (oldR d hn hm Γ f).rho .right d.xE = LER d hm Γ f+1
  newE : (newR d hn hm Γ f).rho .right d.xE = LER d hm Γ f+d.es.length
  Cdecreases : (newR d hn hm Γ f).rho .right d.xC < (oldR d hn hm Γ f).rho .right d.xC
  Eincreases : (oldR d hn hm Γ f).rho .right d.xE < (newR d hn hm Γ f).rho .right d.xE
  sumBalance : endpointSumR d Γ (oldR d hn hm Γ f)+d.es.length =
    endpointSumR d Γ (newR d hn hm Γ f)+d.outer0.length
  otherOld : ∀ {A : NormalForm P} (z : At d.K A) (hc : z.index ≠ d.xC.index) (he : z.index ≠ d.xE.index),
    (oldR d hn hm Γ f).rho .right z = 2+f.rho .right (d.originalViaE z hc he)
  otherNew : ∀ {A : NormalForm P} (z : At d.K A) (hc : z.index ≠ d.xC.index) (he : z.index ≠ d.xE.index),
    (newR d hn hm Γ f).rho .right z = 2+f.rho .right (d.originalViaE z hc he)

theorem rightLaws (d : Disjoint.Data P) (hn : 2 ≤ d.outer0.length) (hm : 2 ≤ d.es.length)
    (Γ : List (NormalForm P)) (f : G P Γ d.F) : RightLaws d hn hm Γ f :=
  ⟨denoteR ..,oldR_count ..,newR_count ..,cutFreeR ..,atomizedR ..,
    oldR_atomized ..,newR_atomized ..,relationR ..,old_xCR ..,new_xCR ..,
    old_xER ..,new_xER ..,C_decreasesR ..,E_increasesR ..,sum_balanceR ..,
    (fun z hc he => other_oldR d hn hm Γ f z hc he),
    (fun z hc he => other_newR d hn hm Γ f z hc he)⟩

theorem fixedGap_right (C E : NormalForm P) (pre post hs : List (List (NormalForm P)))
    (H U V Θ Γ : List (NormalForm P))
    (hn : 2 ≤ (pre++(U++(repeated E (H::hs)++V))::post).length) (hm : 2 ≤ (H::hs).length)
    (f : G P Γ ((repeated C pre++U)++repeated E (H::hs)++(V++C::(repeated C post++Θ)))) :
    RightLaws (Disjoint.fixedGap C E pre post hs H U V Θ) hn hm Γ f := rightLaws ..

end DosenPetric.Reduced.Gentzen.W1.DisjointContraction
