module

public import DosenPetric.GentzenDisjRightFirstNative

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace DisjLogical

theorem rightFirstParent_denote {Γ Θ Δ Λ I D : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P (A :: C :: Γ) Δ) (g : G P (B :: Θ) Λ) (h : G P I (C :: D)) :
    ofTerm (G.cut h ((HeadRouting.front [.disj A B] (Γ ++ Θ) C).left (G.disjL (Γ := C :: Γ) (Θ := Θ) f g))).denote =
      comp (rightFirstInput (.disj A B) Γ Θ I)
        (comp (disjPair
          (comp (assocR .conj A (ante Γ) (ante I))
            (splice (ofTerm h.denote) (comp ((sideM P .conj).cross C A (ante Γ)) (ofTerm f.denote)))) (ofTerm g.denote))
          (rightFirstOutput Δ Λ D)) := by
  have hg : ofTerm ((HeadRouting.front [.disj A B] (Γ ++ Θ) C).left (G.disjL (Γ := C :: Γ) (Θ := Θ) f g)).denote =
      comp (comp
        (tensor .conj (id C) (tensor .conj (id (.disj A B)) (ofTerm (append .conj Γ Θ).invTerm)))
        (comp (firstDisjInput C (ante Γ) (ante Θ) (.disj A B))
          (disjPair (ofTerm f.denote) (ofTerm g.denote)))) (ofTerm (append .disj Δ Λ).toTerm) := by
    rw [ExchangeScript.left_denote,disjL_denote]
    simp only [Laws.assoc]
    erw [← Laws.assoc ((HeadRouting.front [.disj A B] (Γ ++ Θ) C).arrow .conj),head_first_input]
    simp only [Laws.assoc]
  rw [cut_splice,hg,Splice.output,Splice.context,disjL_right_first_core]
  have he := congrArg (fun p => comp p
    (comp (disjPair
      (comp (assocR .conj A (ante Γ) (ante I))
        (splice (ofTerm h.denote) (comp ((sideM P .conj).cross C A (ante Γ)) (ofTerm f.denote)))) (ofTerm g.denote))
      (rightFirstOutput Δ Λ D))) (right_first_parent_input (.disj A B) Γ Θ I)
  simpa only [List.cons_append,List.nil_append,rightFirstOutput,Laws.assoc] using he

theorem disjRightFirstNative_denote {Γ Θ Δ Λ I D : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P (A :: C :: Γ) Δ) (g : G P (B :: Θ) Λ) (h : G P I (C :: D)) :
    ofTerm (disjRightFirstNative (G.cut h ((HeadRouting.front [A] Γ C).left f)) g).denote =
      comp (rightFirstInput (.disj A B) Γ Θ I)
        (comp (disjPair
          (comp (assocR .conj A (ante Γ) (ante I))
            (splice (ofTerm h.denote) (comp ((sideM P .conj).cross C A (ante Γ)) (ofTerm f.denote)))) (ofTerm g.denote))
          (rightFirstOutput Δ Λ D)) := by
  unfold disjRightFirstNative
  rw [ExchangeScript.right_denote,ExchangeScript.left_denote,disjL_denote,
    cut_splice,ExchangeScript.left_denote,HeadRouting.front_singleton]
  have hc := split_cons .conj A Γ I
  dsimp only [side,sideM,conjMonoidal,category,split] at hc
  simp only [List.cons_append,List.nil_append]
  rw [hc]
  have hk : comp (comp (tensor .conj (id A) (ofTerm (append .conj Γ I).invTerm))
      (assocR .conj A (ante Γ) (ante I)))
      (comp (splice (ofTerm h.denote) (comp ((sideM P .conj).cross C A (ante Γ)) (ofTerm f.denote)))
        (ofTerm (append .disj Δ D).toTerm)) =
      comp (comp (tensor .conj (id A) (ofTerm (append .conj Γ I).invTerm))
        (comp (assocR .conj A (ante Γ) (ante I))
          (splice (ofTerm h.denote) (comp ((sideM P .conj).cross C A (ante Γ)) (ofTerm f.denote)))))
        (ofTerm (append .disj Δ D).toTerm) := by
    simp only [Laws.assoc]
  erw [hk,disjPair_output_first,disjPair_input_first]
  simp only [Laws.assoc]
  erw [← Laws.assoc (tensor .conj (id (.disj A B)) (ofTerm (append .conj (Γ ++ I) Θ).invTerm)),
    ← Laws.assoc ((BinaryLogical.lastExchange (.disj A B :: Γ) I Θ).arrow .conj),right_first_input]
  rw [right_first_output]

theorem disjRightFirstNative_equation {Γ Θ Δ Λ I D : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P (A :: C :: Γ) Δ) (g : G P (B :: Θ) Λ) (h : G P I (C :: D)) :
    ofTerm (G.cut h ((HeadRouting.front [.disj A B] (Γ ++ Θ) C).left (G.disjL (Γ := C :: Γ) (Θ := Θ) f g))).denote =
      ofTerm (disjRightFirstNative (G.cut h ((HeadRouting.front [A] Γ C).left f)) g).denote :=
  (rightFirstParent_denote f g h).trans (disjRightFirstNative_denote f g h).symm

end DisjLogical
end DosenPetric.Reduced.Gentzen
