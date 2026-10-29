module

public import DosenPetric.GentzenBlockedConjCore
public import DosenPetric.GentzenBlockedMixNative

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.BlockedConj
universe u
variable {P : Type u}

def headParent {Y F H D E : List (NormalForm P)} {A B C : NormalForm P}
    (p : Route Y F) (q : Route Y H) (f : G P (C::F) (A::D)) (g : G P (C::H) (B::E)) :
    G P (C::Y) (.conj A B::(D++E)) :=
  ((p.head C).append (q.head C)).program.left (G.conjR f g)

def parallel {Y F H D E I R : List (NormalForm P)} {A B : NormalForm P}
    (p : Route Y F) (q : Route Y H)
    (k : G P (F++I) (A::(D++R))) (l : G P (H++I) (B::(E++R))) :
    G P (Y++I) (.conj A B::((D++E)++R)) :=
  (BlockedMix.inputRoute q p I).program.left
    (((BlockedMix.outputRoute E D R).head (.conj A B)).program.right (G.conjR k l))

theorem headParent_denote {Y F H D E : List (NormalForm P)} {A B C : NormalForm P}
    (p : Route Y F) (q : Route Y H) (f : G P (C::F) (A::D)) (g : G P (C::H) (B::E)) :
    ofTerm (headParent p q f g).denote =
      comp (sharedParent (p.sideArrow .conj) (q.sideArrow .conj)
        (ofTerm f.denote) (ofTerm g.denote))
        (tensor .disj (id (.conj A B)) (ofTerm (append .disj D E).toTerm)) := by
  rw [headParent,StructuralProgram.left_denote,Route.program_arrow]
  change comp _ (ofTerm (Rules.conjRight f.denote g.denote)) = _
  simp only [Rules.conjRight,ofTerm_comp,ofTerm_tensor,ofTerm_id]
  rw [← Laws.assoc]
  have he := Route.append_split .conj (p.head C) (q.head C)
  rw [Route.head_side,Route.head_side] at he
  dsimp only [side,sideD,sideM,conjMonoidal,category,split,conjDiagonal,DiagonalData.pair] at he
  erw [he]
  change comp (pair (tensor .conj (id C) (p.sideArrow .conj))
      (tensor .conj (id C) (q.sideArrow .conj))) _ = _
  rw [← Laws.assoc,BlockedMix.pair_tensor]
  unfold sharedParent
  simp only [Laws.assoc]

theorem append_head (A : NormalForm P) (D R : List (NormalForm P)) :
    ofTerm (append .disj (A::D) R).toTerm =
      comp (assocL .disj A (succ D) (succ R))
        (tensor .disj (id A) (ofTerm (append .disj D R).toTerm)) := rfl

theorem parallel_count {Y F H D E I R : List (NormalForm P)} {A B : NormalForm P}
    (p : Route Y F) (q : Route Y H)
    (k : G P (F++I) (A::(D++R))) (l : G P (H++I) (B::(E++R))) :
    (parallel p q k l).cutCount = k.cutCount+l.cutCount := by
  simp only [parallel,StructuralProgram.left_count,StructuralProgram.right_count,G.cutCount]

theorem parallel_denote {Y F H D E I R : List (NormalForm P)} {A B C : NormalForm P}
    (p : Route Y F) (q : Route Y H) (f : G P (C::F) (A::D)) (g : G P (C::H) (B::E))
    (h : G P I (C::R)) :
    ofTerm (parallel p q (G.cut h f) (G.cut h g)).denote =
      comp (ofTerm (append .conj Y I).invTerm)
        (comp (BlockedMix.sharedInput (q.sideArrow .conj) (p.sideArrow .conj))
          (comp (tensor .conj
            (comp (splice (ofTerm h.denote) (ofTerm f.denote)) (assocL .disj A (succ D) (succ R)))
            (comp (splice (ofTerm h.denote) (ofTerm g.denote)) (assocL .disj B (succ E) (succ R))))
            (comp (ofTerm (Term.mixedDisj A (.disj (succ D) (succ R)) B (.disj (succ E) (succ R))))
              (tensor .disj (id (.conj A B))
                (comp (BlockedMix.sharedOutput (succ D) (succ E) (succ R))
                  (comp (tensor .disj (ofTerm (append .disj D E).toTerm) (id (succ R)))
                    (ofTerm (append .disj (D++E) R).toTerm))))))) := by
  rw [parallel,StructuralProgram.left_denote,StructuralProgram.right_denote,
    Route.program_arrow,Route.program_arrow,Route.head_side]
  dsimp only [side,sideM,disjMonoidal,opposite,category]
  change comp _ (comp (ofTerm (Rules.conjRight (G.cut h f).denote (G.cut h g).denote)) _) = _
  simp only [Rules.conjRight,ofTerm_comp,ofTerm_tensor,ofTerm_id]
  rw [cut_splice,cut_splice,append_head,append_head]
  have ht : tensor .conj
      (comp (ofTerm (append .conj F I).invTerm)
        (comp (splice (ofTerm h.denote) (ofTerm f.denote))
          (comp (assocL .disj A (succ D) (succ R))
            (tensor .disj (id A) (ofTerm (append .disj D R).toTerm)))))
      (comp (ofTerm (append .conj H I).invTerm)
        (comp (splice (ofTerm h.denote) (ofTerm g.denote))
          (comp (assocL .disj B (succ E) (succ R))
            (tensor .disj (id B) (ofTerm (append .disj E R).toTerm))))) =
      comp (tensor .conj (ofTerm (append .conj F I).invTerm) (ofTerm (append .conj H I).invTerm))
        (comp (tensor .conj
          (comp (splice (ofTerm h.denote) (ofTerm f.denote)) (assocL .disj A (succ D) (succ R)))
          (comp (splice (ofTerm h.denote) (ofTerm g.denote)) (assocL .disj B (succ E) (succ R))))
          (tensor .conj (tensor .disj (id A) (ofTerm (append .disj D R).toTerm))
            (tensor .disj (id B) (ofTerm (append .disj E R).toTerm)))) := by
    simp only [Laws.tensor_comp,Laws.assoc]
  rw [ht]
  simp only [Laws.assoc]
  have hm := mixedDisj_nat (id A) (ofTerm (append .disj D R).toTerm)
    (id B) (ofTerm (append .disj E R).toTerm)
  rw [Laws.tensor_id] at hm
  rw [← Laws.assoc (tensor .conj (tensor .disj (id A) (ofTerm (append .disj D R).toTerm))
    (tensor .disj (id B) (ofTerm (append .disj E R).toTerm)))]
  erw [← hm]
  simp only [Laws.assoc]
  rw [← Laws.assoc (tensor .disj (id (.conj A B))
    (tensor .disj (ofTerm (append .disj D R).toTerm) (ofTerm (append .disj E R).toTerm))),
    Laws.tensor_comp,Laws.id_comp]
  rw [Laws.tensor_comp,Laws.id_comp]
  simp only [Laws.assoc]
  erw [BlockedMix.output_square]
  rw [← Laws.assoc ((BlockedMix.inputRoute q p I).sideArrow .conj),
    ← Laws.assoc (comp ((BlockedMix.inputRoute q p I).sideArrow .conj)
      (ofTerm (append .conj (F++I) (H++I)).invTerm)),
    Laws.assoc ((BlockedMix.inputRoute q p I).sideArrow .conj),BlockedMix.input_square_conj]
  simp only [Laws.assoc]

end DosenPetric.Reduced.Gentzen.BlockedConj
