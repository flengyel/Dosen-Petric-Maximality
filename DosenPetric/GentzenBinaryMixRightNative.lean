module

public import DosenPetric.GentzenBinaryMixInputRoutes

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace BinaryMix

def rightLeading {I Θ D Λ T J : List (NormalForm P)}
    (g : G P Θ Λ) (k : G P (T ++ I) (J ++ D)) :
    G P ((Θ ++ T) ++ I) ((Λ ++ J) ++ D) :=
  (ExchangeScript.appendAssoc Λ J D).inverse.right
    ((ExchangeScript.appendAssoc Θ T I).inverse.left (G.mix k g))

def rightInput (Θ T I : List (NormalForm P)) :
    Hom (ante ((Θ ++ T) ++ I)) (.conj (ante Θ) (.conj (ante T) (ante I))) :=
  comp (ofTerm (append .conj (Θ ++ T) I).invTerm)
    (comp (tensor .conj (ofTerm (append .conj Θ T).invTerm) (id (ante I)))
      (assocL .conj (ante Θ) (ante T) (ante I)))

def rightOutput (Λ J D : List (NormalForm P)) :
    Hom (.disj (succ Λ) (.disj (succ J) (succ D))) (succ ((Λ ++ J) ++ D)) :=
  comp (assocR .disj (succ Λ) (succ J) (succ D))
    (comp (tensor .disj (ofTerm (append .disj Λ J).toTerm) (id (succ D)))
      (ofTerm (append .disj (Λ ++ J) D).toTerm))

theorem rightLeading_denote {I Θ D Λ T J : List (NormalForm P)} {C : NormalForm P}
    (f : G P I (C :: D)) (g : G P Θ Λ) (h : G P (C :: T) J) :
    ofTerm (rightLeading g (G.cut f h)).denote =
      comp (rightInput Θ T I)
        (comp (tensor .conj (ofTerm g.denote) (splice (ofTerm f.denote) (ofTerm h.denote)))
          (comp (mix (succ Λ) (.disj (succ J) (succ D))) (rightOutput Λ J D))) := by
  unfold rightLeading
  rw [ExchangeScript.right_denote,ExchangeScript.left_denote]
  change comp (comp _ (ofTerm (Rules.mix (G.cut f h).denote g.denote))) _ = _
  simp only [Rules.mix,ofTerm_comp,ofTerm_tensor,mix_term]
  rw [cut_splice]
  have ht : tensor .conj (ofTerm g.denote)
      (comp (ofTerm (append .conj T I).invTerm)
        (comp (splice (ofTerm f.denote) (ofTerm h.denote)) (ofTerm (append .disj J D).toTerm))) =
      comp (tensor .conj (id (ante Θ)) (ofTerm (append .conj T I).invTerm))
        (comp (tensor .conj (ofTerm g.denote) (splice (ofTerm f.denote) (ofTerm h.denote)))
          (tensor .conj (id (succ Λ)) (ofTerm (append .disj J D).toTerm))) := by
    simp only [Laws.tensor_comp,Laws.id_comp,Laws.comp_id]
  rw [ht]
  simp only [Laws.assoc]
  rw [← Laws.assoc (tensor .conj (id (succ Λ)) (ofTerm (append .disj J D).toTerm)),← Laws.mix_nat]
  simp only [Laws.assoc]
  have hi : comp ((ExchangeScript.appendAssoc Θ T I).inverse.arrow .conj)
      (comp (ofTerm (append .conj Θ (T ++ I)).invTerm)
        (tensor .conj (id (ante Θ)) (ofTerm (append .conj T I).invTerm))) = rightInput Θ T I :=
    split_assoc_inverse .conj Θ T I
  have ho : comp (tensor .disj (id (succ Λ)) (ofTerm (append .disj J D).toTerm))
      (comp (ofTerm (append .disj Λ (J ++ D)).toTerm)
        ((ExchangeScript.appendAssoc Λ J D).inverse.arrow .disj)) = rightOutput Λ J D := by
    have he := split_assoc_inverse .disj Λ J D
    dsimp only [side,category,opposite,sideM,disjMonoidal,split,rightOutput] at he ⊢
    simpa only [Laws.assoc] using he
  erw [ho]
  have he := congrArg (fun k => comp k
    (comp (tensor .conj (ofTerm g.denote) (splice (ofTerm f.denote) (ofTerm h.denote)))
      (comp (mix (succ Λ) (.disj (succ J) (succ D))) (rightOutput Λ J D)))) hi
  simpa only [Laws.assoc] using he

theorem right_cut_denote {I Θ D Λ T J : List (NormalForm P)} {C : NormalForm P}
    (f : G P I (C :: D)) (g : G P Θ Λ) (h : G P (C :: T) J) :
    ofTerm (G.cut f ((HeadRouting.front Θ T C).left (G.mix h g))).denote =
      comp (rightInput Θ T I)
        (comp (tensor .conj (ofTerm g.denote) (splice (ofTerm f.denote) (ofTerm h.denote)))
          (comp (mix (succ Λ) (.disj (succ J) (succ D))) (rightOutput Λ J D))) := by
  have hh : ofTerm ((HeadRouting.front Θ T C).left (G.mix h g)).denote =
      comp (tensor .conj (id C) (ofTerm (append .conj Θ T).invTerm))
        (comp ((sideM P .conj).cross C (ante Θ) (ante T))
          (comp (tensor .conj (ofTerm g.denote) (ofTerm h.denote))
            (comp (mix (succ Λ) (succ J)) (ofTerm (append .disj Λ J).toTerm)))) := by
    rw [ExchangeScript.left_denote]
    change comp _ (ofTerm (Rules.mix h.denote g.denote)) = _
    simp only [Rules.mix,ofTerm_comp,ofTerm_tensor,mix_term]
    have he : comp ((HeadRouting.front Θ T C).arrow .conj)
        (ofTerm (append .conj Θ (C :: T)).invTerm) =
        comp (tensor .conj (id C) (ofTerm (append .conj Θ T).invTerm))
          ((sideM P .conj).cross C (ante Θ) (ante T)) := HeadRouting.front_split .conj Θ T C
    rw [← Laws.assoc,he]
    simp only [Laws.assoc]
  rw [cut_splice,hh,Splice.context]
  have hs : splice (ofTerm f.denote)
      (comp ((sideM P .conj).cross C (ante Θ) (ante T))
        (comp (tensor .conj (ofTerm g.denote) (ofTerm h.denote))
          (comp (mix (succ Λ) (succ J)) (ofTerm (append .disj Λ J).toTerm)))) =
      comp (splice (ofTerm f.denote)
        (comp ((sideM P .conj).cross C (ante Θ) (ante T))
          (comp (tensor .conj (ofTerm g.denote) (ofTerm h.denote)) (mix (succ Λ) (succ J)))))
        (tensor .disj (ofTerm (append .disj Λ J).toTerm) (id (succ D))) := by
    simpa only [Laws.assoc] using Splice.output (ofTerm f.denote)
      (comp ((sideM P .conj).cross C (ante Θ) (ante T))
        (comp (tensor .conj (ofTerm g.denote) (ofTerm h.denote)) (mix (succ Λ) (succ J))))
      (ofTerm (append .disj Λ J).toTerm)
  rw [hs,splice_mix_right]
  simp only [rightInput,rightOutput,Laws.assoc]

theorem rightLeading_equation {I Θ D Λ T J : List (NormalForm P)} {C : NormalForm P}
    (f : G P I (C :: D)) (g : G P Θ Λ) (h : G P (C :: T) J) :
    ofTerm (G.cut f ((HeadRouting.front Θ T C).left (G.mix h g))).denote =
      ofTerm (rightLeading g (G.cut f h)).denote :=
  (right_cut_denote f g h).trans (rightLeading_denote f g h).symm

end BinaryMix
end DosenPetric.Reduced.Gentzen
