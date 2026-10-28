module

public import DosenPetric.GentzenCutConstants

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

def discardLast (C : NormalForm P) (Θ : List (NormalForm P)) :
    StructuralProgram P (Θ++[C]) Θ :=
  .seq (.thin Θ [] C) (nilProgram Θ)

theorem discardLast_atomic (C : NormalForm P) (Θ : List (NormalForm P))
    (hc : AtomicFormula C) : (discardLast C Θ).Atomic := ⟨hc,True.intro⟩

theorem discardLast_get (C : NormalForm P) (Θ : List (NormalForm P))
    {A : NormalForm P} (a : At Θ A) : (discardLast C Θ).get a = a.before [C] := by
  apply At.index_injective
  change ((Route.thin Θ [] C).get (a.cast (List.append_nil Θ).symm)).index = _
  rw [thin_index,At.index_cast,At.index_before]
  rw [ite_eq_left a.index_lt]

theorem discardLast_arrow (C : NormalForm P) (Θ : List (NormalForm P)) (o : Op) :
    (discardLast C Θ).arrow o = (side P o).comp (split o Θ [C])
      ((sideD P o).fst (fold o Θ) (fold o [C])) := by
  have he : (side P o).comp (join o Θ [C]) ((discardLast C Θ).arrow o) =
      (sideD P o).fst (fold o Θ) (fold o [C]) := by
    apply side_ext o
    intro A a
    rw [(side P o).assoc,StructuralProgram.component]
    rw [discardLast_get,join_before]
  have hh := congrArg (fun k => (side P o).comp (split o Θ [C]) k) he
  rw [←(side P o).assoc,split_join,(side P o).id_comp] at hh
  exact hh

theorem inr_append_single (C : NormalForm P) (Δ : List (NormalForm P)) :
    comp (inr (succ [C]) (succ Δ)) (ofTerm (append .disj [C] Δ).toTerm) = inr C (succ Δ) := by
  apply side_ext .disj
  intro A a
  have h := congrArg (fun k => (side P .disj).comp (split .disj [C] Δ) k)
    (join_shift .disj [C] a)
  rw [←(side P .disj).assoc,split_join,(side P .disj).id_comp] at h
  change comp (ofTerm a.injection) (inr C (succ Δ)) =
    comp (comp (ofTerm a.injection) (inr (succ [C]) (succ Δ)))
      (ofTerm (append .disj [C] Δ).toTerm) at h
  change comp (ofTerm a.injection)
    (comp (inr (succ [C]) (succ Δ)) (ofTerm (append .disj [C] Δ).toTerm)) =
      comp (ofTerm a.injection) (inr C (succ Δ))
  simpa only [Laws.assoc] using h.symm

namespace CutBase
variable {C : NormalForm P} {Γ Θ Δ Λ : List (NormalForm P)}

def leftThinningRepair (g : G P Θ Λ) : G P (Θ++[C]) (Λ++[]) :=
  (nilProgram Λ).right ((discardLast C Θ).left g)

theorem leftThinningRepair_count (g : G P Θ Λ) :
    (leftThinningRepair (C:=C) g).cutCount = g.cutCount := by
  rw [leftThinningRepair,StructuralProgram.right_count,StructuralProgram.left_count]

theorem leftThinningRepair_atomized (g : G P Θ Λ) (hc : AtomicFormula C) (hg : g.Atomized) :
    (leftThinningRepair (C:=C) g).Atomized := by
  unfold leftThinningRepair
  apply StructuralProgram.right_atomized (nilProgram Λ) (by trivial)
  exact StructuralProgram.left_atomized _ (discardLast_atomic C Θ hc) g hg

/-- An endomorphism in the cut slot is discarded by the right premise's
fresh left thinning. This includes both atomic identity and atomic zero. -/
theorem endomorphism_thinning (f : G P [C] [C]) (g : G P Θ Λ) :
    ofTerm (G.cut f (G.thinL [] Θ Λ C g)).denote =
      ofTerm (leftThinningRepair (C:=C) g).denote := by
  rw [G.denote_cut,G.denote_thinL]
  have hl : ofTerm (Route.thin [] Θ C).product = snd C (ante Θ) := thin_head .conj C Θ
  rw [hl,dist_bot]
  have hs : comp (swap .conj (ante Θ) C) (snd C (ante Θ)) = fst (ante Θ) C := by
    rw [Laws.snd_swap C (ante Θ),←Laws.assoc,Laws.swap_swap,Laws.id_comp]
  rw [←Laws.assoc (swap .conj (ante Θ) C),hs]
  simp only [Laws.assoc]
  rw [←Laws.assoc (rightIn .disj (.conj (ante Θ) C)),Laws.rightIn_nat]
  simp only [Laws.assoc]
  rw [←Laws.assoc (tensor .conj (id (ante Θ)) (ofTerm f.denote)),Laws.tensor_comp,Laws.id_comp]
  have hf : comp (tensor .conj (id (ante Θ)) (comp (ofTerm f.denote) (rightOut .disj C)))
      (fst (ante Θ) C) = fst (ante Θ) (ante [C]) :=
    (Laws.fst_nat (id (ante Θ)) (comp (ofTerm f.denote) (rightOut .disj C))).symm.trans
      (Laws.comp_id _)
  rw [←Laws.assoc (tensor .conj (id (ante Θ)) (comp (ofTerm f.denote) (rightOut .disj C))),hf]
  rw [leftThinningRepair,StructuralProgram.right_denote,StructuralProgram.left_denote,
    discardLast_arrow C Θ .conj,nilProgram_arrow .disj]
  change _ = comp (comp (comp (ofTerm (append .conj Θ [C]).invTerm)
    (fst (ante Θ) (ante [C]))) (ofTerm g.denote))
    (comp (rightIn .disj (succ Λ)) (ofTerm (append .disj Λ []).toTerm))
  simp only [Laws.assoc]

/-- The dual thinning equation discards the entire right endomorphism. -/
theorem thinning_endomorphism (f : G P Γ Δ) (g : G P [C] [C]) :
    ofTerm (G.cut (G.thinR Γ [] Δ C f) g).denote =
      ofTerm (G.thinR Γ [] Δ C f).denote := by
  rw [G.denote_cut,G.denote_thinR]
  have hr : ofTerm (Route.thin [] Δ C).coproduct = inr C (succ Δ) := thin_head .disj C Δ
  rw [hr,dist_top]
  simp only [Laws.assoc]
  change comp (leftIn .conj (ante Γ))
    (comp (tensor .conj (id .top) (comp (ofTerm f.denote) (inr C (succ Δ))))
      (comp (leftOut .conj (.disj C (succ Δ)))
        (comp (tensor .disj (leftIn .conj C) (id (succ Δ)))
          (comp (tensor .disj (comp (swap .conj .top C) (ofTerm g.denote)) (id (succ Δ)))
            (ofTerm (append .disj [C] Δ).toTerm))))) = _
  rw [←Laws.assoc (leftIn .conj (ante Γ)),Laws.leftIn_nat]
  simp only [Laws.assoc]
  rw [←Laws.assoc (leftIn .conj (.disj C (succ Δ))),Laws.leftIn_Out,Laws.id_comp,
    ←Laws.assoc (tensor .disj (leftIn .conj C) (id (succ Δ))),Laws.tensor_comp,Laws.id_comp]
  rw [←Laws.assoc (inr C (succ Δ)),Laws.inr_nat]
  rw [Laws.assoc,inr_append_single]
  rw [Laws.id_comp]
end CutBase
end DosenPetric.Reduced.Gentzen
