module

public import DosenPetric.GentzenRightContractionHead

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric
universe u v
namespace MonoidalData
variable {O : Type u} {C : Category.{u,v} O} (M : MonoidalData C)

def firstExtract (A Q D E : O) :
    C.Hom (M.obj A (M.obj Q (M.obj D E))) (M.obj Q (M.obj (M.obj A D) E)) :=
  C.comp (M.cross A Q (M.obj D E)) (M.tensor (C.id Q) (M.assocR A D E))

def secondExtract (A Q D E : O) :
    C.Hom (M.obj A (M.obj Q (M.obj D E))) (M.obj Q (M.obj D (M.obj A E))) :=
  C.comp (M.cross A Q (M.obj D E)) (M.tensor (C.id Q) (M.cross A D E))

end MonoidalData
namespace DiagonalData
variable {O : Type u} {C : Category.{u,v} O} {M : MonoidalData C} (D : DiagonalData M)
variable (hu : ∀ A B, C.comp (M.assocR A B M.unit) (M.rightOut (M.obj A B)) =
  M.tensor (C.id A) (M.rightOut B))
variable (hs : ∀ A B, C.comp (M.swap A B) (D.snd B A) = D.fst A B)

include hu hs in
theorem double_extraction (A Z Q E F : O) :
    C.comp (M.cross A Z (M.obj Q (M.obj E F)))
      (C.comp (M.tensor (C.id Z) (M.secondExtract A Q E F))
        (M.firstExtract Z Q E (M.obj A F))) =
      C.comp (M.tensor (C.id A) (M.firstExtract Z Q E F))
        (M.secondExtract A Q (M.obj Z E) F) := by
  simp only [MonoidalData.firstExtract,MonoidalData.secondExtract,MonoidalData.cross,
    D.assocR_pair hu,D.assocL_pair hu,D.swap_pair hs,D.tensor_pair,D.pair_pre,
    D.pair_fst,D.pair_snd,D.pair_fst_comp,D.pair_snd_comp,C.comp_id,C.assoc]

end DiagonalData
namespace Reduced.Gentzen.DoubleConjSplice
variable {P : Type u}

def firstOutput (C Q D E : NormalForm P) :
    Hom (.disj Q (.disj (.disj C D) E)) (.disj C (.disj Q (.disj D E))) :=
  comp (tensor .disj (id Q) (assocL .disj C D E)) ((sideM P .disj).cross C Q (.disj D E))

def secondOutput (C Q D E : NormalForm P) :
    Hom (.disj Q (.disj D (.disj C E))) (.disj C (.disj Q (.disj D E))) :=
  comp (tensor .disj (id Q) ((sideM P .disj).cross C D E)) ((sideM P .disj).cross C Q (.disj D E))

theorem between_square (C Z Q D E : NormalForm P) :
    comp (firstOutput Z Q D (.disj C E))
      (comp (tensor .disj (id Z) (secondOutput C Q D E))
        ((sideM P .disj).cross C Z (.disj Q (.disj D E)))) =
      comp (secondOutput C Q (.disj Z D) E) (tensor .disj (id C) (firstOutput Z Q D E)) := by
  have he := (disjDiagonal P).double_extraction (rightIn_assocL .disj) (side_swap_snd .disj) C Z Q D E
  dsimp only [MonoidalData.firstExtract,MonoidalData.secondExtract,disjMonoidal,
    disjDiagonal,opposite,category] at he
  simpa only [firstOutput,secondOutput,MonoidalData.cross,sideM,side,disjMonoidal,
    opposite,category,Laws.assoc] using he

end Reduced.Gentzen.DoubleConjSplice
end DosenPetric
