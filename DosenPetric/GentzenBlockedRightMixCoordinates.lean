module

public import DosenPetric.GentzenBlockedRightMixCore
public import DosenPetric.GentzenBlockedMixCoordinates

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.BlockedMix
universe u
variable {P : Type u}

def rightInputRoute (I Θ Γ : List (NormalForm P)) :
    Route (I++(Θ++Γ)) ((I++Θ)++(I++Γ)) :=
  ((Route.identity I).parallel (Route.takeFirst Θ Γ)).append
    ((Route.identity I).parallel (Route.takeSecond Θ Γ))

def rightOutputRoute {Y F H : List (NormalForm P)} (p : Route Y F) (q : Route Y H)
    (J : List (NormalForm P)) : Route (J++Y) ((J++H)++(J++F)) :=
  ((Route.identity J).parallel q).append ((Route.identity J).parallel p)

theorem right_output_square (o : Op) {Y F H : List (NormalForm P)}
    (p : Route Y F) (q : Route Y H) (J : List (NormalForm P)) :
    (side P o).comp ((rightOutputRoute p q J).sideArrow o)
      ((side P o).comp (split o (J++H) (J++F))
        ((sideM P o).tensor (split o J H) (split o J F))) =
      (side P o).comp (split o J Y)
        ((sideD P o).pair
          ((sideM P o).tensor ((side P o).id (fold o J)) (q.sideArrow o))
          ((sideM P o).tensor ((side P o).id (fold o J)) (p.sideArrow o))) := by
  let S := side P o
  let D := sideD P o
  rw [rightOutputRoute,← S.assoc,Route.append_split]
  apply D.ext
  · rw [S.assoc,← D.fst_nat,← S.assoc,D.pair_fst,
      S.assoc,D.pair_fst,Route.parallel_split,Route.identity_arrow]
  · rw [S.assoc,← D.snd_nat,← S.assoc,D.pair_snd,
      S.assoc,D.pair_snd,Route.parallel_split,Route.identity_arrow]

theorem right_input_square (I Θ Γ : List (NormalForm P)) :
    comp ((rightInputRoute I Θ Γ).sideArrow .conj)
      (comp (ofTerm (append .conj (I++Θ) (I++Γ)).invTerm)
        (tensor .conj (ofTerm (append .conj I Θ).invTerm) (ofTerm (append .conj I Γ).invTerm))) =
      comp (ofTerm (append .conj I (Θ++Γ)).invTerm)
        (comp (tensor .conj (id (ante I)) (ofTerm (append .conj Θ Γ).invTerm))
          (rightSharedInput (ante I) (ante Θ) (ante Γ))) := by
  have he := right_output_square .conj (Route.takeSecond Θ Γ) (Route.takeFirst Θ Γ) I
  rw [Route.takeFirst_arrow,Route.takeSecond_arrow] at he
  dsimp only [side,sideD,sideM,conjMonoidal,category,split,DiagonalData.pair,conjDiagonal] at he
  change _ = comp (ofTerm (append .conj I (Θ++Γ)).invTerm)
    (pair
      (tensor .conj (id (ante I)) (comp (ofTerm (append .conj Θ Γ).invTerm) (fst (ante Θ) (ante Γ))))
      (tensor .conj (id (ante I)) (comp (ofTerm (append .conj Θ Γ).invTerm) (snd (ante Θ) (ante Γ))))) at he
  change comp ((rightInputRoute I Θ Γ).sideArrow .conj) _ = _ at he
  rw [he]
  unfold rightSharedInput
  simp only [ProductCalculation.pair_pre,Laws.tensor_comp,Laws.id_comp]

/-- Repair both fixed contexts after the two original child cuts. -/
def rightParallel {Y F H Γ Θ I J : List (NormalForm P)}
    (p : Route Y F) (q : Route Y H)
    (k : G P (I++Γ) (J++F)) (l : G P (I++Θ) (J++H)) :
    G P (I++(Θ++Γ)) (J++Y) :=
  (rightInputRoute I Θ Γ).program.left ((rightOutputRoute p q J).program.right (G.mix k l))

theorem rightParallel_count {Y F H Γ Θ I J : List (NormalForm P)}
    (p : Route Y F) (q : Route Y H)
    (k : G P (I++Γ) (J++F)) (l : G P (I++Θ) (J++H)) :
    (rightParallel p q k l).cutCount = k.cutCount+l.cutCount := by
  simp only [rightParallel,StructuralProgram.left_count,StructuralProgram.right_count,G.cutCount]

end DosenPetric.Reduced.Gentzen.BlockedMix
