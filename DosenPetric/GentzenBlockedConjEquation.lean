module

public import DosenPetric.GentzenBlockedConjSource

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.BlockedConj
universe u
variable {P : Type u}

theorem parent_fold (Q : NormalForm P) (D E R : List (NormalForm P)) :
    comp (tensor .disj (tensor .disj (id Q) (ofTerm (append .disj D E).toTerm)) (id (succ R)))
      (ofTerm (append .disj (Q::(D++E)) R).toTerm) =
      comp (assocL .disj Q (.disj (succ D) (succ E)) (succ R))
        (tensor .disj (id Q)
          (comp (tensor .disj (ofTerm (append .disj D E).toTerm) (id (succ R)))
            (ofTerm (append .disj (D++E) R).toTerm))) := by
  rw [append_head,← Laws.assoc,← Laws.assocL_nat]
  simp only [Laws.assoc,Laws.tensor_comp,Laws.id_comp]

theorem headParent_equation {Y F H D E I R : List (NormalForm P)} {A B C : NormalForm P}
    (p : Route Y F) (q : Route Y H) (f : G P (C::F) (A::D)) (g : G P (C::H) (B::E))
    (h : G P I (C::R)) :
    ofTerm (G.cut h (headParent p q f g)).denote =
      ofTerm (parallel p q (G.cut h f) (G.cut h g)).denote := by
  rw [cut_splice,headParent_denote,Splice.output,parallel_denote]
  simp only [Laws.assoc]
  rw [parent_fold]
  rw [← Laws.assoc (splice (ofTerm h.denote)
    (sharedParent (p.sideArrow .conj) (q.sideArrow .conj) (ofTerm f.denote) (ofTerm g.denote))),
    shared_splice]
  simp only [Laws.assoc,Laws.tensor_comp,Laws.id_comp]

end DosenPetric.Reduced.Gentzen.BlockedConj
