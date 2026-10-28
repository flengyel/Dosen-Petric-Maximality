module

public import DosenPetric.GentzenCutBase

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

/-- Retain the explicit right-empty list transport on either sequent side. -/
def nilProgram (Γ : List (NormalForm P)) : StructuralProgram P (Γ++[]) Γ :=
  (StructuralProgram.identity Γ).reindex (List.append_nil Γ).symm rfl

theorem nilProgram_arrow (o : Op) (Γ : List (NormalForm P)) :
    (nilProgram Γ).arrow o = (side P o).comp (split o Γ [])
      ((sideM P o).rightOut (fold o Γ)) := by
  have he : (side P o).comp (join o Γ []) ((nilProgram Γ).arrow o) =
      (sideM P o).rightOut (fold o Γ) := by
    apply side_ext o
    intro A a
    rw [(side P o).assoc,StructuralProgram.component]
    have ha : (nilProgram Γ).get a = a.before [] := by
      apply At.index_injective
      simp only [nilProgram,StructuralProgram.get,At.index_cast,At.index_before]
    rw [ha,join_before,(sideD P o).fst_unit]
  have hh := congrArg (fun k => (side P o).comp (split o Γ []) k) he
  rw [←(side P o).assoc,split_join,(side P o).id_comp] at hh
  exact hh

namespace CutBase
variable {Γ Θ Δ Λ : List (NormalForm P)}

def topRepair (g : G P Θ Λ) : G P (Θ++[]) (Λ++[]) :=
  (nilProgram Λ).right ((nilProgram Θ).left g)

theorem topRepair_count (g : G P Θ Λ) : (topRepair g).cutCount = g.cutCount := by
  rw [topRepair,StructuralProgram.right_count,StructuralProgram.left_count]

theorem topRepair_atomized (g : G P Θ Λ) (h : g.Atomized) : (topRepair g).Atomized := by
  unfold topRepair
  apply StructuralProgram.right_atomized (nilProgram Λ) (by trivial)
  exact StructuralProgram.left_atomized (nilProgram Θ) (by trivial) g h

theorem top_thinning (g : G P Θ Λ) :
    ofTerm (G.cut G.topI (G.thinL [] Θ Λ .top g)).denote =
      ofTerm (topRepair g).denote := by
  rw [G.denote_cut,G.denote_topI,G.denote_thinL]
  have hl : ofTerm (Route.thin [] Θ .top).product = snd .top (ante Θ) := thin_head .conj .top Θ
  rw [hl]
  have hs : comp (swap .conj (ante Θ) .top) (snd .top (ante Θ)) = rightOut .conj (ante Θ) := by
    rw [swap_snd,Laws.fst_top]
  rw [←Laws.assoc (swap .conj (ante Θ) .top),hs,dist_bot]
  simp only [Laws.assoc]
  rw [←Laws.assoc (tensor .conj (id (ante Θ)) (rightIn .disj .top)),
    Laws.tensor_comp,Laws.rightIn_Out,Laws.id_comp,Laws.tensor_id,Laws.id_comp]
  rw [←Laws.assoc (rightIn .disj (.conj (ante Θ) .top)),Laws.rightIn_nat]
  rw [topRepair,StructuralProgram.right_denote,StructuralProgram.left_denote,
    nilProgram_arrow .conj,nilProgram_arrow .disj]
  change _ = comp (comp (comp (ofTerm (append .conj Θ []).invTerm)
    (rightOut .conj (ante Θ))) (ofTerm g.denote))
    (comp (rightIn .disj (succ Λ)) (ofTerm (append .disj Λ []).toTerm))
  simp only [Laws.assoc]

theorem thinning_bot (f : G P Γ Δ) :
    ofTerm (G.cut (G.thinR Γ [] Δ .bot f) G.botE).denote = ofTerm f.denote := by
  rw [G.denote_cut,G.denote_thinR,G.denote_botE]
  have hr : ofTerm (Route.thin [] Δ .bot).coproduct = inr .bot (succ Δ) := thin_head .disj .bot Δ
  rw [hr,dist_top]
  simp only [Laws.assoc]
  change comp (leftIn .conj (ante Γ))
    (comp (tensor .conj (id .top) (comp (ofTerm f.denote) (inr .bot (succ Δ))))
      (comp (leftOut .conj (.disj .bot (succ Δ)))
        (comp (tensor .disj (leftIn .conj .bot) (id (succ Δ)))
          (comp (tensor .disj (comp (swap .conj .top .bot) (rightOut .conj .bot)) (id (succ Δ)))
            (leftOut .disj (succ Δ)))))) = _
  rw [←Laws.assoc (leftIn .conj (ante Γ)),Laws.leftIn_nat]
  simp only [Laws.assoc]
  rw [←Laws.assoc (leftIn .conj (.disj .bot (succ Δ))),Laws.leftIn_Out,Laws.id_comp,
    ←Laws.assoc (tensor .disj (leftIn .conj .bot) (id (succ Δ))),Laws.tensor_comp,Laws.id_comp]
  have hb : comp (leftIn .conj (.bot : NormalForm P))
      (comp (swap .conj .top .bot) (rightOut .conj .bot)) = id .bot := by
    rw [←Laws.assoc,swap_unit_in,Laws.rightIn_Out]
  rw [hb,Laws.tensor_id,Laws.id_comp]
  have hi : inr (.bot : NormalForm P) (succ Δ) = leftIn .disj (succ Δ) :=
    (disjDiagonal P).snd_unit _
  rw [hi,Laws.leftIn_Out,Laws.comp_id]
end CutBase
end DosenPetric.Reduced.Gentzen
