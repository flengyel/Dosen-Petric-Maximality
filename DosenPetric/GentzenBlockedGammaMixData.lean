module

public import DosenPetric.GentzenBlockedMixSource
public import DosenPetric.GentzenBlockedSource

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.BlockedMix
universe u
variable {P : Type u}

/-- The two selected copies in the source's reversed native mix order. -/
def gammaBlock (C : NormalForm P) (X Y Z T : List (NormalForm P)) :
    ContractionBlock P ((Z++C::T)++(X++C::Y)) (gaps [Z,T++X]++C::Y) :=
  ⟨C,[Z,T++X],Y,by
    simp only [repeated,List.append_assoc,List.cons_append,List.nil_append],rfl⟩

def firstTag (C : NormalForm P) (X Y : List (NormalForm P)) : At (X++C::Y) C :=
  At.shift X (.here C Y)

def gammaParent {C : NormalForm P} {X Y Z T Δ Λ : List (NormalForm P)}
    (f : G P (X++C::Y) Δ) (g : G P (Z++C::T) Λ) :
    G P (gaps [Z,T++X]++C::Y) (Λ++Δ) :=
  (gammaBlock C X Y Z T).applyL (Nat.le_refl 2) (Λ++Δ) (G.mix f g)

theorem gammaParent_source {C : NormalForm P} {X Y Z T Δ Λ : List (NormalForm P)}
    (f : G P (X++C::Y) Δ) (g : G P (Z++C::T) Λ) :
    gammaParent f g = BlockedSource.left2 C Z (T++X) Y (Λ++Δ)
      ((G.mix f g).reindex
        (by simp only [List.append_assoc,List.cons_append]) rfl) := by
  simp only [gammaParent,gammaBlock,ContractionBlock.applyL,BlockedSource.left2,G.reindex_trans]
  rfl

theorem gamma_first (C : NormalForm P) (X Y Z T : List (NormalForm P)) :
    (gammaBlock C X Y Z T).route.secondBlock.get (firstTag C X Y) =
      (gammaBlock C X Y Z T).keep := by
  apply At.index_injective
  rw [Route.secondBlock_get,ContractionBlock.get_index,ContractionBlock.keep_index]
  simp only [gammaBlock,firstTag,At.index_shift,At.index,List.length_append,List.length_cons,
    Nat.add_zero,gaps,List.append_nil,List.length_nil,copyIndex]
  repeat first | split | omega
  all_goals simp_all only [not_true_eq_false]

theorem gamma_second (C : NormalForm P) (X Y Z T : List (NormalForm P)) :
    (gammaBlock C X Y Z T).route.firstBlock.get (firstTag C Z T) =
      (gammaBlock C X Y Z T).keep := by
  apply At.index_injective
  rw [Route.firstBlock_get,ContractionBlock.get_index,ContractionBlock.keep_index]
  simp only [gammaBlock,firstTag,At.index_before,At.index_shift,At.index,Nat.add_zero,
    gaps,List.append_nil,List.length_append,List.length_nil,copyIndex]
  repeat first | split | omega
  all_goals simp_all only [not_true_eq_false]

theorem gamma_first_fixed (C : NormalForm P) (X Y Z T : List (NormalForm P))
    {B : NormalForm P} (v : At (firstTag C X Y).erase B) :
    ((gammaBlock C X Y Z T).route.secondBlock.get ((firstTag C X Y).retain v)).index ≠
      (gammaBlock C X Y Z T).keep.index := by
  have hn := (firstTag C X Y).retain_ne v
  have hi := ((firstTag C X Y).retain v).index_lt
  rw [Route.secondBlock_get,ContractionBlock.get_index,ContractionBlock.keep_index,At.index_shift]
  have hx : (firstTag C X Y).index = X.length := by
    simp only [firstTag,At.index_shift,At.index,Nat.add_zero]
  rw [hx] at hn
  simp only [List.length_append,List.length_cons] at hi
  simp only [gammaBlock,gaps,List.append_nil,List.length_append,List.length_cons,
    List.length_nil,copyIndex]
  repeat first | split | omega
  all_goals simp_all only [not_true_eq_false]

theorem gamma_second_fixed (C : NormalForm P) (X Y Z T : List (NormalForm P))
    {B : NormalForm P} (v : At (firstTag C Z T).erase B) :
    ((gammaBlock C X Y Z T).route.firstBlock.get ((firstTag C Z T).retain v)).index ≠
      (gammaBlock C X Y Z T).keep.index := by
  have hn := (firstTag C Z T).retain_ne v
  have hi := ((firstTag C Z T).retain v).index_lt
  rw [Route.firstBlock_get,ContractionBlock.get_index,ContractionBlock.keep_index,At.index_before]
  have hx : (firstTag C Z T).index = Z.length := by
    simp only [firstTag,At.index_shift,At.index,Nat.add_zero]
  rw [hx] at hn
  simp only [List.length_append,List.length_cons] at hi
  simp only [gammaBlock,gaps,List.append_nil,List.length_append,List.length_nil,copyIndex]
  repeat first | split | omega
  all_goals simp_all only [not_true_eq_false]

def gammaFirstRoute (C : NormalForm P) (X Y Z T : List (NormalForm P)) :
    Route (gammaBlock C X Y Z T).keep.erase (firstTag C X Y).erase :=
  Route.selectedResidual (gammaBlock C X Y Z T).route.secondBlock
    (gammaBlock C X Y Z T).keep (firstTag C X Y) (gamma_first_fixed C X Y Z T)

def gammaSecondRoute (C : NormalForm P) (X Y Z T : List (NormalForm P)) :
    Route (gammaBlock C X Y Z T).keep.erase (firstTag C Z T).erase :=
  Route.selectedResidual (gammaBlock C X Y Z T).route.firstBlock
    (gammaBlock C X Y Z T).keep (firstTag C Z T) (gamma_second_fixed C X Y Z T)

end DosenPetric.Reduced.Gentzen.BlockedMix
