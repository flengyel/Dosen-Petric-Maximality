module

public import DosenPetric.GentzenMixedRepresentation

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

theorem cut_pure_out {Γ : List (NormalForm P)} {B C : NormalForm P}
    (f : G P Γ [B]) (g : G P [B] [C]) :
    comp (ofTerm (G.cut f g).denote) (rightOut .disj C) =
      comp (comp (ofTerm f.denote) (rightOut .disj B)) (decode g.denote) := by
  rw [cut_pure]
  simp only [decode, Laws.assoc]

namespace Represented

theorem dist (A B C : NormalForm P) : Represented (Reduced.dist A B C) := by
  obtain ⟨s, hs⟩ := swap .conj B A
  let q : G P [B, A] [.conj A B] := G.cut (G.conjR (G.identityNF B) (G.identityNF A)) s
  have hq : Reduced.comp (ofTerm q.denote) (Reduced.rightOut .disj (.conj A B)) =
      Reduced.comp (Reduced.tensor .conj (Reduced.id B) (Reduced.rightOut .conj A))
        (Reduced.swap .conj B A) := by
    dsimp only [q]
    rw [cut_pure_out, G.collectConj_out, hs]
  have hl : Reduced.comp (Reduced.tensor .conj (Reduced.rightIn .conj A) (Reduced.id B))
      (Reduced.comp (Reduced.swap .conj (ante [A]) B)
        (Reduced.comp (ofTerm q.denote) (Reduced.rightOut .disj (.conj A B)))) =
        Reduced.id (.conj A B) := by
    rw [hq, ← Laws.assoc (Reduced.tensor .conj (Reduced.rightIn .conj A) (Reduced.id B)),
      ← Laws.swap_nat]
    simp only [Laws.assoc]
    rw [← Laws.assoc (Reduced.tensor .conj (Reduced.id B) (Reduced.rightIn .conj A)),
      Laws.tensor_comp, Laws.id_comp, Laws.rightIn_Out, Laws.tensor_id, Laws.id_comp, Laws.swap_swap]
  let r : G P [.conj A (.disj B C)] [.disj (.conj A B) C] :=
    .conjL [] [] [.disj (.conj A B) C] A (.disj B C)
      (.disjR [A, .disj B C] [] [] (.conj A B) C (.cut (G.splitDisj B C) q))
  refine ⟨r, ?_⟩
  change Reduced.comp (Reduced.rightIn .conj (.conj A (.disj B C)))
    (Reduced.comp (Reduced.comp (Reduced.assocL .conj A (.disj B C) .top)
      (Reduced.comp (Reduced.comp (ofTerm (append .conj [A] [.disj B C]).invTerm)
        (Reduced.comp (Reduced.tensor .conj (Reduced.id (ante [A])) (ofTerm (G.splitDisj B C).denote))
          (Reduced.comp (Reduced.dist (ante [A]) B (succ [C]))
            (Reduced.comp (Reduced.tensor .disj (Reduced.comp (Reduced.swap .conj (ante [A]) B)
              (ofTerm q.denote)) (Reduced.id (succ [C]))) (ofTerm (append .disj [.conj A B] [C]).toTerm)))))
        (Reduced.assocR .disj (.conj A B) C .bot))) (Reduced.rightOut .disj (.disj (.conj A B) C))) = _
  simp only [← Laws.assoc]
  rw [single_split_left, Laws.tensor_comp, Laws.comp_id, G.splitDisj_in]
  simp only [Laws.assoc]
  rw [single_join]
  rw [← Laws.assoc (Reduced.tensor .conj (Reduced.rightIn .conj A)
      (Reduced.tensor .disj (Reduced.id B) (Reduced.rightIn .disj C))), ← Laws.dist_nat]
  simp only [Laws.assoc]
  rw [Laws.tensor_comp]
  simp only [Laws.assoc]
  rw [Laws.tensor_comp]
  simp only [Laws.id_comp]
  rw [hl, Laws.rightIn_Out, Laws.tensor_id, Laws.comp_id]

end Represented
end DosenPetric.Reduced.Gentzen
