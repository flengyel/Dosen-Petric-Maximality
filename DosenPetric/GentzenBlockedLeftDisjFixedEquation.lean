module

public import DosenPetric.GentzenBlockedLeftDisjFixedCoordinates

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.BlockedLeftDisj
universe u
variable {P : Type u}

theorem parent_fixed {C F H D E : NormalForm P} (A B : NormalForm P)
    (k : Hom (.conj C F) D) (l : Hom (.conj C H) E) :
    comp (parent C F H A B) (tensor .disj (fixedMap A k) (fixedMap B l)) =
      comp (tensor .conj (id C) (fst (.conj F H) (.disj A B)))
        (BlockedMix.sharedParent (snd F H) (fst F H) l k) := by
  have hf {V W : NormalForm P} (Q : NormalForm P) (v : Hom (.conj C V) W) :
      comp (assocL .conj C V Q) (fixedMap Q v) = comp (fst (.conj C V) Q) v := by
    rw [fixedMap,← Laws.assoc,assocL_drop]
  have ht : tensor .disj (comp (fst (.conj C F) A) k) (comp (fst (.conj C H) B) l) =
      comp (tensor .disj (fst (.conj C F) A) (fst (.conj C H) B)) (tensor .disj k l) := by
    rw [Laws.tensor_comp]
  have hd : comp (assocR .conj C (.conj F H) (.disj A B))
      (fst (.conj C (.conj F H)) (.disj A B)) =
      tensor .conj (id C) (fst (.conj F H) (.disj A B)) := by
    have he := (conjDiagonal P).assocR_fst (rightOut_assocR .conj) C (.conj F H) (.disj A B)
    exact he
  unfold parent
  simp only [Laws.assoc]
  rw [Laws.tensor_comp,hf,hf,ht]
  rw [← Laws.assoc (ofTerm (Rules.sourceConj (.conj C F) (.conj C H) A B)),sourceConj_fst]
  simp only [Laws.assoc]
  rw [Laws.mix_nat]
  rw [← Laws.assoc (tensor .conj
      (pair (tensor .conj (id C) (fst F H)) (tensor .conj (id C) (snd F H))) (id (.disj A B))),
    ← Laws.fst_nat]
  simp only [Laws.assoc]
  rw [← Laws.assoc (assocR .conj C (.conj F H) (.disj A B)),hd]
  rfl

theorem reconstruction_fixed {C F H D E : NormalForm P} (A B R : NormalForm P)
    (k : Hom (.conj C F) D) (l : Hom (.conj C H) E) :
    comp (reconstruction C F H A B R)
      (tensor .disj (tensor .disj (fixedMap A k) (fixedMap B l)) (id R)) =
      comp (tensor .conj (fst (.conj F H) (.disj A B)) (id (.disj C R)))
        (splice (id (.disj C R)) (BlockedMix.sharedParent (snd F H) (fst F H) l k)) := by
  unfold reconstruction
  simp only [Laws.assoc]
  rw [sharedOutput_natural]
  rw [← Laws.assoc (tensor .disj
      (comp (terminalCross F (.disj C R) A) (kernel (.conj F A) C R))
      (comp (terminalCross H (.disj C R) B) (kernel (.conj H B) C R))),Laws.tensor_comp]
  simp only [Laws.assoc]
  rw [child_fixed,child_fixed]
  have ht : tensor .disj
      (comp (fst (.conj F (.disj C R)) A) (splice (id (.disj C R)) k))
      (comp (fst (.conj H (.disj C R)) B) (splice (id (.disj C R)) l)) =
      comp (tensor .disj (fst (.conj F (.disj C R)) A) (fst (.conj H (.disj C R)) B))
        (tensor .disj (splice (id (.disj C R)) k) (splice (id (.disj C R)) l)) := by
    rw [Laws.tensor_comp]
  rw [ht]
  simp only [Laws.assoc]
  rw [← Laws.assoc (ofTerm (Rules.sourceConj (.conj F (.disj C R)) (.conj H (.disj C R)) A B)),
    sourceConj_fst]
  simp only [Laws.assoc]
  rw [← Laws.assoc (mix (.conj F (.disj C R)) (.conj H (.disj C R))),Laws.mix_nat]
  simp only [Laws.assoc]
  rw [← Laws.assoc (input F H (.disj A B) (.disj C R)),input_drop]
  rw [BlockedMix.shared_splice]
  simp only [Laws.assoc]

theorem fixed_equation {C F H D E : NormalForm P} (A B R : NormalForm P)
    (k : Hom (.conj C F) D) (l : Hom (.conj C H) E) :
    comp (comp (kernel (.conj (.conj F H) (.disj A B)) C R)
      (tensor .disj (parent C F H A B) (id R)))
      (tensor .disj (tensor .disj (fixedMap A k) (fixedMap B l)) (id R)) =
      comp (reconstruction C F H A B R)
        (tensor .disj (tensor .disj (fixedMap A k) (fixedMap B l)) (id R)) := by
  rw [Laws.assoc,Laws.tensor_comp,parent_fixed,Laws.id_comp,reconstruction_fixed]
  rw [kernel,← Splice.output,Laws.id_comp,Splice.context]

end DosenPetric.Reduced.Gentzen.BlockedLeftDisj
