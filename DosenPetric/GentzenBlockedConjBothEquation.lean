module

public import DosenPetric.GentzenBlockedConjBothData

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.BlockedConjBoth
universe u
variable {P : Type u}

theorem selected_parent {A B : NormalForm P} {Γ Θ X Y Z T : List (NormalForm P)}
    (f : G P Γ (A::(X++.conj A B::Y))) (g : G P Θ (B::(Z++.conj A B::T))) :
    ofTerm ((block A B X Y Z T).keep.toHead.right (parent f g)).denote =
      ofTerm (SequentialConjBoth.parent (firstResidue A B X Y Z T) (secondResidue A B X Y Z T)
        (SequentialConjFirst.firstChild (BlockedMix.firstTag (.conj A B) X Y) f)
        (SequentialConjSecond.secondChild (BlockedMix.firstTag (.conj A B) Z T) g)).denote := by
  rw [ExchangeScript.right_denote,parent,ContractionBlock.denoteR]
  exact SequentialConjBoth.source_denote _ _ _ _ _ _
    (fresh_get A B X Y Z T) (first_get A B X Y Z T) (second_get A B X Y Z T)
    (fun v => (Route.selectedResidual_get _ _ _ _ v).symm)
    (fun v => (Route.selectedResidual_get _ _ _ _ v).symm) f g

theorem source_equation {A B : NormalForm P} {Γ Θ X Y Z T I J : List (NormalForm P)}
    (f : G P Γ (A::(X++.conj A B::Y))) (g : G P Θ (B::(Z++.conj A B::T)))
    (h : G P I J) (z : At I (.conj A B)) :
    ofTerm (PositionalCut.cut (parent f g) (block A B X Y Z T).keep h z).denote =
      ofTerm (SequentialConjBoth.rebuild (.conj A B) (firstResidue A B X Y Z T) (secondResidue A B X Y Z T)
        (G.cut (SequentialConjBoth.fresh
          (G.cut (SequentialConjBoth.child A (.conj A B)
            (SequentialConjFirst.firstChild (BlockedMix.firstTag (.conj A B) X Y) f)) (z.toHead.left h))
          (G.cut (SequentialConjBoth.child B (.conj A B)
            (SequentialConjSecond.secondChild (BlockedMix.firstTag (.conj A B) Z T) g)) (z.toHead.left h)))
          (z.toHead.left h))).denote := by
  apply (Rules.cut_congr (selected_parent f g) (g:=(z.toHead.left h).denote) rfl).trans
  exact SequentialConjBoth.native_equation (firstResidue A B X Y Z T) (secondResidue A B X Y Z T)
    (SequentialConjFirst.firstChild (BlockedMix.firstTag (.conj A B) X Y) f)
    (SequentialConjSecond.secondChild (BlockedMix.firstTag (.conj A B) Z T) g) (z.toHead.left h)

end DosenPetric.Reduced.Gentzen.BlockedConjBoth
