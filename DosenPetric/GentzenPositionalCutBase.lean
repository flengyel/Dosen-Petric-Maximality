module

public import DosenPetric.GentzenSelectedThinning
public import DosenPetric.GentzenLeafShapes

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace PositionalCut

/-- A cut-free atomized representative at the positional cut's exact output sequent. -/
def Eliminated {Γ Δ Θ Λ : List (NormalForm P)} {C : NormalForm P}
    (f : G P Γ Δ) (x : At Δ C) (g : G P Θ Λ) (y : At Θ C) : Prop :=
  ∃ h : G P (y.erase ++ Γ) (Λ ++ x.erase),
    h.CutFree ∧ h.Atomized ∧ ofTerm h.denote = ofTerm (cut f x g y).denote

theorem thin_thin (Γ Δ Λ F U V : List (NormalForm P)) (C : NormalForm P)
    (f : G P Γ (Δ ++ Λ)) (g : G P (F ++ U) V)
    (hf : f.CutFree) (hg : g.CutFree) (af : f.Atomized) (ag : g.Atomized) :
    Eliminated (G.thinR Γ Δ Λ C f) (At.shift Δ (.here C Λ))
      (G.thinL F U V C g) (At.shift F (.here C U)) := by
  let f' := f.reindex rfl (At.erase_shift Δ Λ C).symm
  let g' := g.reindex (At.erase_shift F U C).symm rfl
  refine ⟨G.mix f' g', ?_, ?_, ?_⟩
  · change f'.cutCount + g'.cutCount = 0
    simp only [f', g', G.count_reindex]
    exact Nat.add_eq_zero_iff.mpr ⟨hf,hg⟩
  · exact ⟨(G.atomized_reindex ..).mpr af, (G.atomized_reindex ..).mpr ag⟩
  · exact ((Rules.cut_congr (G.toHead_thinR_denote Γ Δ Λ C f)
      (G.toHead_thinL_denote F U V C g)).trans (CutBase.thinned_thinned C f' g')).symm

theorem endomorphism_thin {Γ Θ Λ : List (NormalForm P)} (C : NormalForm P)
    (f : G P [C] [C]) (g : G P (Γ ++ Θ) Λ)
    (hg : g.CutFree) (ag : g.Atomized) (hc : AtomicFormula C) :
    Eliminated f (.here C []) (G.thinL Γ Θ Λ C g) (At.shift Γ (.here C Θ)) := by
  let g' := g.reindex (At.erase_shift Γ Θ C).symm rfl
  refine ⟨CutBase.leftThinningRepair (C := C) g', ?_, ?_, ?_⟩
  · change (CutBase.leftThinningRepair (C := C) g').cutCount = 0
    rw [CutBase.leftThinningRepair_count, G.count_reindex]
    exact hg
  · exact CutBase.leftThinningRepair_atomized g' hc ((G.atomized_reindex ..).mpr ag)
  · exact ((Rules.cut_congr rfl (G.toHead_thinL_denote Γ Θ Λ C g)).trans
      (CutBase.endomorphism_thinning f g')).symm

theorem thin_endomorphism {Γ Δ Λ : List (NormalForm P)} (C : NormalForm P)
    (f : G P Γ (Δ ++ Λ)) (g : G P [C] [C])
    (hf : f.CutFree) (af : f.Atomized) (hc : AtomicFormula C) :
    Eliminated (G.thinR Γ Δ Λ C f) (At.shift Δ (.here C Λ)) g (.here C []) := by
  let f' := f.reindex rfl (At.erase_shift Δ Λ C).symm
  refine ⟨G.thinR Γ [] (At.shift Δ (.here C Λ)).erase C f', ?_, ?_, ?_⟩
  · change f'.cutCount = 0
    rw [G.count_reindex]
    exact hf
  · exact ⟨hc, (G.atomized_reindex ..).mpr af⟩
  · exact ((Rules.cut_congr (G.toHead_thinR_denote Γ Δ Λ C f) rfl).trans
      (CutBase.thinning_endomorphism f' g)).symm

theorem top_thin (Γ Θ Λ : List (NormalForm P)) (g : G P (Γ ++ Θ) Λ)
    (hg : g.CutFree) (ag : g.Atomized) :
    Eliminated G.topI (.here .top []) (G.thinL Γ Θ Λ .top g) (At.shift Γ (.here .top Θ)) := by
  let g' := g.reindex (At.erase_shift Γ Θ (.top : NormalForm P)).symm rfl
  refine ⟨CutBase.topRepair g', ?_, ?_, ?_⟩
  · change (CutBase.topRepair g').cutCount = 0
    rw [CutBase.topRepair_count, G.count_reindex]
    exact hg
  · exact CutBase.topRepair_atomized g' ((G.atomized_reindex ..).mpr ag)
  · exact ((Rules.cut_congr rfl (G.toHead_thinL_denote Γ Θ Λ .top g)).trans
      (CutBase.top_thinning g')).symm

theorem thin_bot (Γ Δ Λ : List (NormalForm P)) (f : G P Γ (Δ ++ Λ))
    (hf : f.CutFree) (af : f.Atomized) :
    Eliminated (G.thinR Γ Δ Λ .bot f) (At.shift Δ (.here .bot Λ)) G.botE (.here .bot []) := by
  let f' := f.reindex rfl (At.erase_shift Δ Λ (.bot : NormalForm P)).symm
  refine ⟨f', ?_, (G.atomized_reindex ..).mpr af, ?_⟩
  · change f'.cutCount = 0
    rw [G.count_reindex]
    exact hf
  · exact ((Rules.cut_congr (G.toHead_thinR_denote Γ Δ Λ .bot f) rfl).trans
      (CutBase.thinning_bot f')).symm

end PositionalCut
end DosenPetric.Reduced.Gentzen
