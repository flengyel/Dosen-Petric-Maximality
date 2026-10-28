module

public import DosenPetric.GentzenCleanCuts

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

theorem decode_injective {A B : NormalForm P}
    (s t : Term P (ante [A]) (succ [B])) (h : decode s = decode t) :
    ofTerm s = ofTerm t := by
  have he := congrArg (fun k => comp (rightOut .conj A) (comp k (rightIn .disj B))) h
  simpa only [decode,Laws.assoc,←Laws.assoc (rightOut .conj A),
    Laws.rightOut_In,Laws.id_comp,Laws.rightOut_In,Laws.comp_id] using he

namespace CutBase

theorem identity_identity (l : Literal P) :
    ofTerm (G.cut (G.identity l) (G.identity l)).denote = ofTerm (G.identity l).denote := by
  apply decode_injective
  rw [cut_single]
  simp only [G.denote,decode_encode,ofTerm_id,Laws.comp_id]

theorem zero_identity (l : Literal P) :
    ofTerm (G.cut (G.zero l) (G.identity l)).denote = ofTerm (G.zero l).denote := by
  apply decode_injective
  rw [cut_single]
  simp only [G.denote,decode_encode,ofTerm_id,Laws.comp_id]

theorem identity_zero (l : Literal P) :
    ofTerm (G.cut (G.identity l) (G.zero l)).denote = ofTerm (G.zero l).denote := by
  apply decode_injective
  rw [cut_single]
  simp only [G.denote,decode_encode,ofTerm_id,Laws.id_comp]

theorem zero_zero (l : Literal P) :
    ofTerm (G.cut (G.zero l) (G.zero l)).denote = ofTerm (G.zero l).denote := by
  apply decode_injective
  rw [cut_single]
  simp only [G.denote,decode_encode]
  exact zero_idempotent _

/-- Cutting two newly thinned occurrences gives native mix. This equation
also holds before atomization, for an arbitrary cut formula. -/
theorem thinned_thinned {Γ Θ Δ Λ : List (NormalForm P)} (C : NormalForm P)
    (f : G P Γ Δ) (g : G P Θ Λ) :
    ofTerm (G.cut (G.thinR Γ [] Δ C f) (G.thinL [] Θ Λ C g)).denote =
      ofTerm (G.mix f g).denote := by
  rw [G.denote_cut,G.denote_thinL,G.denote_thinR]
  have hl : ofTerm (Route.thin [] Θ C).product = snd C (ante Θ) := thin_head .conj C Θ
  have hr : ofTerm (Route.thin [] Δ C).coproduct = inr C (succ Δ) := thin_head .disj C Δ
  rw [hl,hr]
  change comp (ofTerm (append .conj Θ Γ).invTerm)
    (comp (tensor .conj (id (ante Θ)) (comp (ofTerm f.denote) (inr C (succ Δ))))
      (comp (dist (ante Θ) C (succ Δ))
        (comp (tensor .disj (comp (swap .conj (ante Θ) C) (comp (snd C (ante Θ)) (ofTerm g.denote)))
          (id (succ Δ))) (ofTerm (append .disj Λ Δ).toTerm)))) = _
  have hs : comp (swap .conj (ante Θ) C) (snd C (ante Θ)) = fst (ante Θ) C := by
    rw [Laws.snd_swap C (ante Θ),←Laws.assoc,Laws.swap_swap,Laws.id_comp]
  rw [←Laws.assoc (swap .conj (ante Θ) C),hs]
  have ht : tensor .disj (comp (fst (ante Θ) C) (ofTerm g.denote)) (id (succ Δ)) =
      comp (tensor .disj (fst (ante Θ) C) (id (succ Δ)))
        (tensor .disj (ofTerm g.denote) (id (succ Δ))) := by
    rw [Laws.tensor_comp,Laws.id_comp]
  rw [tensor_factor .conj (id (ante Θ)) (ofTerm f.denote) (inr C (succ Δ)),ht]
  have hm : comp (comp (tensor .conj (id (ante Θ)) (inr C (succ Δ))) (dist (ante Θ) C (succ Δ)))
      (tensor .disj (fst (ante Θ) C) (id (succ Δ))) = mix (ante Θ) (succ Δ) :=
    (Laws.assoc ..).trans (Laws.dist_mix (ante Θ) C (succ Δ)).symm
  simp only [Laws.assoc]
  rw [←Laws.assoc (tensor .conj (id (ante Θ)) (inr C (succ Δ))),
    ←Laws.assoc (comp (tensor .conj (id (ante Θ)) (inr C (succ Δ))) (dist (ante Θ) C (succ Δ))),
    hm]
  rw [←Laws.assoc (mix (ante Θ) (succ Δ)),Laws.mix_nat]
  simp only [Laws.assoc]
  rw [←Laws.assoc (tensor .conj (id (ante Θ)) (ofTerm f.denote)),
    Laws.tensor_comp,Laws.id_comp,Laws.comp_id]
  rfl
end CutBase
end DosenPetric.Reduced.Gentzen
