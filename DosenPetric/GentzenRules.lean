module

public import DosenPetric.GentzenRouting

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

namespace Rules

def conjLeft (Γ Θ : List (NormalForm P)) (A B : NormalForm P) :
    Iso (ante (Γ ++ .conj A B :: Θ)) (ante (Γ ++ A :: B :: Θ)) := by
  simpa only [fold_as_foldr, List.foldr_append, List.foldr_cons] using
    under .conj Γ (Iso.assoc .conj A B (ante Θ))

def disjRight (Δ Λ : List (NormalForm P)) (A B : NormalForm P) :
    Iso (succ (Δ ++ A :: B :: Λ)) (succ (Δ ++ .disj A B :: Λ)) := by
  simpa only [fold_as_foldr, List.foldr_append, List.foldr_cons] using
    under .disj Δ (Iso.assoc .disj A B (succ Λ)).symm

/-- The displayed e'-conjunction on p.240, with explicit binary association. -/
def sourceConj (X Y A B : NormalForm P) :
    Term P (.conj (.conj X Y) (.disj A B)) (.disj (.conj X A) (.conj Y B)) :=
  .comp (.tensor .conj (.id (.conj X Y)) (.swap .disj A B))
    (.comp (.assocL .conj X Y (.disj B A))
      (.comp (.tensor .conj (.id X) (.dist Y B A))
        (.comp (.tensor .conj (.id X) (.swap .disj (.conj Y B) A))
          (.dist X A (.conj Y B)))))

def conjRight {Γ Θ Δ Λ : List (NormalForm P)} {A B : NormalForm P}
    (f : Term P (ante Γ) (succ (A :: Δ))) (g : Term P (ante Θ) (succ (B :: Λ))) :
    Term P (ante (Γ ++ Θ)) (succ (.conj A B :: (Δ ++ Λ))) :=
  .comp (append .conj Γ Θ).invTerm
    (.comp (.tensor .conj f g)
      (.comp (Term.mixedDisj A (succ Δ) B (succ Λ))
        (.tensor .disj (.id (.conj A B)) (append .disj Δ Λ).toTerm)))

def disjLeft {Γ Θ Δ Λ : List (NormalForm P)} {A B : NormalForm P}
    (f : Term P (ante (A :: Γ)) (succ Δ)) (g : Term P (ante (B :: Θ)) (succ Λ)) :
    Term P (ante (.disj A B :: (Γ ++ Θ))) (succ (Δ ++ Λ)) :=
  .comp (.tensor .conj (.id (.disj A B)) (append .conj Γ Θ).invTerm)
    (.comp (.swap .conj (.disj A B) (.conj (ante Γ) (ante Θ)))
      (.comp (sourceConj (ante Γ) (ante Θ) A B)
        (.comp (.tensor .disj (.swap .conj (ante Γ) A) (.swap .conj (ante Θ) B))
          (.comp (.tensor .disj f g) (append .disj Δ Λ).toTerm))))

def mix {Γ Θ Δ Λ : List (NormalForm P)}
    (f : Term P (ante Γ) (succ Δ)) (g : Term P (ante Θ) (succ Λ)) :
    Term P (ante (Θ ++ Γ)) (succ (Λ ++ Δ)) :=
  .comp (append .conj Θ Γ).invTerm
    (.comp (.tensor .conj g f)
      (.comp (.mix (succ Λ) (succ Δ)) (append .disj Λ Δ).toTerm))

/-- Contextual cut at the explicitly selected head occurrence of C. -/
def cut {Γ Θ Δ Λ : List (NormalForm P)} {C : NormalForm P}
    (f : Term P (ante Γ) (succ (C :: Δ))) (g : Term P (ante (C :: Θ)) (succ Λ)) :
    Term P (ante (Θ ++ Γ)) (succ (Λ ++ Δ)) :=
  .comp (append .conj Θ Γ).invTerm
    (.comp (.tensor .conj (.id (ante Θ)) f)
      (.comp (.dist (ante Θ) C (succ Δ))
        (.comp (.tensor .disj (.comp (.swap .conj (ante Θ) C) g) (.id (succ Δ)))
          (append .disj Λ Δ).toTerm)))

theorem mixedDisj_positive (A B C D : NormalForm P) : (Term.mixedDisj A B C D).Positive := by
  apply Term.positive_of_labels <;> rfl

theorem sourceConj_positive (A B C D : NormalForm P) : (sourceConj A B C D).Positive := by
  apply Term.positive_of_labels <;> rfl

theorem conjRight_positive {Γ Θ Δ Λ : List (NormalForm P)} {A B : NormalForm P}
    {f : Term P (ante Γ) (succ (A :: Δ))} {g : Term P (ante Θ) (succ (B :: Λ))}
    (hf : f.Positive) (hg : g.Positive) : (conjRight f g).Positive :=
  .comp (append ..).positive_inv (.comp (.tensor _ hf hg)
    (.comp (mixedDisj_positive ..) (.tensor _ (.id _) (append ..).positive_to)))

theorem disjLeft_positive {Γ Θ Δ Λ : List (NormalForm P)} {A B : NormalForm P}
    {f : Term P (ante (A :: Γ)) (succ Δ)} {g : Term P (ante (B :: Θ)) (succ Λ)}
    (hf : f.Positive) (hg : g.Positive) : (disjLeft f g).Positive :=
  .comp (.tensor _ (.id _) (append ..).positive_inv) (.comp (.swap ..)
    (.comp (sourceConj_positive ..) (.comp (.tensor _ (.swap ..) (.swap ..))
      (.comp (.tensor _ hf hg) (append ..).positive_to))))

theorem mix_positive {Γ Θ Δ Λ : List (NormalForm P)}
    {f : Term P (ante Γ) (succ Δ)} {g : Term P (ante Θ) (succ Λ)}
    (hf : f.Positive) (hg : g.Positive) : (mix f g).Positive :=
  .comp (append ..).positive_inv (.comp (.tensor _ hg hf)
    (.comp (.mix ..) (append ..).positive_to))

theorem cut_positive {Γ Θ Δ Λ : List (NormalForm P)} {C : NormalForm P}
    {f : Term P (ante Γ) (succ (C :: Δ))} {g : Term P (ante (C :: Θ)) (succ Λ)}
    (hf : f.Positive) (hg : g.Positive) : (cut f g).Positive :=
  .comp (append ..).positive_inv (.comp (.tensor _ (.id _) hf)
    (.comp (.dist ..) (.comp (.tensor _ (.comp (.swap ..) hg) (.id _)) (append ..).positive_to)))

end Rules
end DosenPetric.Reduced.Gentzen
