module

public import DosenPetric.GentzenDisjRightSecondNative

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace DisjLogical

theorem rightSecondParent_denote {Γ Θ Δ Λ I D : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P (A :: Γ) Δ) (g : G P (B :: C :: Θ) Λ) (h : G P I (C :: D)) :
    ofTerm (G.cut h ((HeadRouting.front (.disj A B :: Γ) Θ C).left (G.disjL f g))).denote =
      comp (rightSecondInput (.disj A B) Γ Θ I)
        (comp (disjPair (ofTerm f.denote)
          (comp (assocR .conj B (ante Θ) (ante I))
            (splice (ofTerm h.denote) (comp ((sideM P .conj).cross C B (ante Θ)) (ofTerm g.denote)))))
          (rightSecondOutput Δ Λ D)) := by
  have hg : ofTerm ((HeadRouting.front (.disj A B :: Γ) Θ C).left (G.disjL f g)).denote =
      comp (comp
        (tensor .conj (id C) (tensor .conj (id (.disj A B)) (ofTerm (append .conj Γ Θ).invTerm)))
        (comp (secondDisjInput C (ante Γ) (ante Θ) (.disj A B))
          (disjPair (ofTerm f.denote) (ofTerm g.denote)))) (ofTerm (append .disj Δ Λ).toTerm) := by
    rw [ExchangeScript.left_denote,disjL_denote]
    simp only [Laws.assoc]
    erw [← Laws.assoc ((HeadRouting.front (.disj A B :: Γ) Θ C).arrow .conj),head_second_input]
    simp only [Laws.assoc]
  rw [cut_splice,hg,Splice.output,Splice.context,disjL_right_second_core]
  have he := congrArg (fun p => comp p
    (comp (disjPair (ofTerm f.denote)
      (comp (assocR .conj B (ante Θ) (ante I))
        (splice (ofTerm h.denote) (comp ((sideM P .conj).cross C B (ante Θ)) (ofTerm g.denote)))))
      (rightSecondOutput Δ Λ D))) (right_second_parent_input (.disj A B) Γ Θ I)
  simpa only [List.cons_append,rightSecondOutput,Laws.assoc] using he

theorem disjRightSecondNative_denote {Γ Θ Δ Λ I D : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P (A :: Γ) Δ) (g : G P (B :: C :: Θ) Λ) (h : G P I (C :: D)) :
    ofTerm (disjRightSecondNative f (G.cut h ((HeadRouting.front [B] Θ C).left g))).denote =
      comp (rightSecondInput (.disj A B) Γ Θ I)
        (comp (disjPair (ofTerm f.denote)
          (comp (assocR .conj B (ante Θ) (ante I))
            (splice (ofTerm h.denote) (comp ((sideM P .conj).cross C B (ante Θ)) (ofTerm g.denote)))))
          (rightSecondOutput Δ Λ D)) := by
  unfold disjRightSecondNative
  rw [ExchangeScript.right_denote,ExchangeScript.left_denote,disjL_denote,
    cut_splice,ExchangeScript.left_denote,HeadRouting.front_singleton]
  have hc := split_cons .conj B Θ I
  dsimp only [side,sideM,conjMonoidal,category,split] at hc
  simp only [List.cons_append,List.nil_append]
  rw [hc]
  have hk : comp (comp (tensor .conj (id B) (ofTerm (append .conj Θ I).invTerm))
      (assocR .conj B (ante Θ) (ante I)))
      (comp (splice (ofTerm h.denote) (comp ((sideM P .conj).cross C B (ante Θ)) (ofTerm g.denote)))
        (ofTerm (append .disj Λ D).toTerm)) =
      comp (comp (tensor .conj (id B) (ofTerm (append .conj Θ I).invTerm))
        (comp (assocR .conj B (ante Θ) (ante I))
          (splice (ofTerm h.denote) (comp ((sideM P .conj).cross C B (ante Θ)) (ofTerm g.denote)))))
        (ofTerm (append .disj Λ D).toTerm) := by
    simp only [Laws.assoc]
  erw [hk,disjPair_output_second,disjPair_input_second]
  simp only [Laws.assoc]
  erw [← Laws.assoc (tensor .conj (id (.disj A B)) (ofTerm (append .conj Γ (Θ ++ I)).invTerm)),
    ← Laws.assoc (((ExchangeScript.appendAssoc Γ Θ I).inverse.consFixed (.disj A B)).arrow .conj),right_second_input]
  rw [right_second_output]

theorem disjRightSecondNative_equation {Γ Θ Δ Λ I D : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P (A :: Γ) Δ) (g : G P (B :: C :: Θ) Λ) (h : G P I (C :: D)) :
    ofTerm (G.cut h ((HeadRouting.front (.disj A B :: Γ) Θ C).left (G.disjL f g))).denote =
      ofTerm (disjRightSecondNative f (G.cut h ((HeadRouting.front [B] Θ C).left g))).denote :=
  (rightSecondParent_denote f g h).trans (disjRightSecondNative_denote f g h).symm

end DisjLogical
end DosenPetric.Reduced.Gentzen
