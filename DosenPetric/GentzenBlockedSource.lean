module

public import DosenPetric.GentzenContractionSelectionCoordinates
public import DosenPetric.GentzenAnalysisMacros

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.BlockedSource
universe u
variable {P : Type u}

/-- The source's terminal conjunction-left, with explicit empty fixed tail. -/
def conjLLast (Γ Δ : List (NormalForm P)) (A B : NormalForm P)
    (f : G P (Γ++[A,B]) Δ) : G P (Γ++[.conj A B]) Δ :=
  G.conjL Γ [] Δ A B f

/-- Move the source's terminal inputs to the primitive heads, then move the
    introduced disjunction from the primitive head to the source's tail. -/
def disjLLast {Γ Θ Δ Λ : List (NormalForm P)} {A B : NormalForm P}
    (f : G P (Γ++[A]) Δ) (g : G P (Θ++[B]) Λ) :
    G P ((Γ++Θ)++[.disj A B]) (Δ++Λ) := by
  let f' : G P (A::Γ) Δ := (G.exchangeL [] Γ [A] [] Δ
    (f.reindex (List.append_nil (Γ++[A])).symm rfl)).reindex
      (by simp only [List.nil_append,List.singleton_append,List.append_nil]) rfl
  let g' : G P (B::Θ) Λ := (G.exchangeL [] Θ [B] [] Λ
    (g.reindex (List.append_nil (Θ++[B])).symm rfl)).reindex
      (by simp only [List.nil_append,List.singleton_append,List.append_nil]) rfl
  let t := @G.disjL P Γ Θ Δ Λ A B f' g'
  exact (G.exchangeL [] [.disj A B] (Γ++Θ) [] (Δ++Λ)
    (t.reindex (by simp only [List.nil_append,List.singleton_append,List.append_nil]) rfl)).reindex
      (by simp only [List.nil_append,List.append_nil]) rfl

theorem disjLLast_count {Γ Θ Δ Λ : List (NormalForm P)} {A B : NormalForm P}
    (f : G P (Γ++[A]) Δ) (g : G P (Θ++[B]) Λ) :
    (disjLLast f g).cutCount = f.cutCount+g.cutCount := by
  simp only [disjLLast,G.count_reindex,G.cutCount]

def left2 (C : NormalForm P) (X Y T Δ : List (NormalForm P))
    (f : G P (X++C::(Y++C::T)) Δ) : G P (gaps [X,Y]++C::T) Δ :=
  G.contractL C [X,Y] T Δ (Nat.le_refl 2)
    (f.reindex (by simp only [repeated,List.append_assoc,List.cons_append,List.nil_append]) rfl)

def left3 (C : NormalForm P) (X Y Z T Δ : List (NormalForm P))
    (f : G P (X++C::(Y++C::(Z++C::T))) Δ) : G P (gaps [X,Y,Z]++C::T) Δ :=
  G.contractL C [X,Y,Z] T Δ (Nat.le_succ 2)
    (f.reindex (by simp only [repeated,List.append_assoc,List.cons_append,List.nil_append]) rfl)

def right2 (C : NormalForm P) (Γ X Y T : List (NormalForm P))
    (f : G P Γ (X++C::(Y++C::T))) : G P Γ (gaps [X,Y]++C::T) :=
  G.contractR Γ C [X,Y] T (Nat.le_refl 2)
    (f.reindex rfl (by simp only [repeated,List.append_assoc,List.cons_append,List.nil_append]))

def right3 (C : NormalForm P) (Γ X Y Z T : List (NormalForm P))
    (f : G P Γ (X++C::(Y++C::(Z++C::T)))) : G P Γ (gaps [X,Y,Z]++C::T) :=
  G.contractR Γ C [X,Y,Z] T (Nat.le_succ 2)
    (f.reindex rfl (by simp only [repeated,List.append_assoc,List.cons_append,List.nil_append]))

/-- The source right-retention order is realized by the existing explicit
    exchange macro, without changing the primitive contraction or its rank. -/
def sourceRight2 (C : NormalForm P) (Γ X Y T : List (NormalForm P))
    (f : G P Γ (repeated C [X,Y]++T)) : G P Γ (X++C::(Y++T)) :=
  (G.contractRFirst Γ X T C [Y] (Nat.le_refl 1) f).reindex rfl
    (by simp only [gaps,List.append_nil])

theorem sourceRight2_count (C : NormalForm P) (Γ X Y T : List (NormalForm P))
    (f : G P Γ (repeated C [X,Y]++T)) :
    (sourceRight2 C Γ X Y T f).cutCount = f.cutCount :=
  by simp only [sourceRight2,G.count_reindex,G.contractRFirst_count]

def sourceRight3 (C : NormalForm P) (Γ X Y Z T : List (NormalForm P))
    (f : G P Γ (repeated C [X,Y,Z]++T)) : G P Γ (X++C::((Y++Z)++T)) :=
  (G.contractRFirst Γ X T C [Y,Z] (Nat.le_succ 1) f).reindex rfl
    (by simp only [gaps,List.append_nil])

theorem sourceRight3_count (C : NormalForm P) (Γ X Y Z T : List (NormalForm P))
    (f : G P Γ (repeated C [X,Y,Z]++T)) :
    (sourceRight3 C Γ X Y Z T f).cutCount = f.cutCount := by
  simp only [sourceRight3,G.count_reindex,G.contractRFirst_count]

theorem selected2_indices (C : NormalForm P) (X Y T : List (NormalForm P)) :
    (selectedCopies C [X,Y] T).map At.index = [X.length,X.length+1+Y.length] :=
  (selectedCopies_indices ..).trans rfl

theorem selected3_indices (C : NormalForm P) (X Y Z T : List (NormalForm P)) :
    (selectedCopies C [X,Y,Z] T).map At.index =
      [X.length,X.length+1+Y.length,X.length+1+(Y.length+1+Z.length)] :=
  (selectedCopies_indices ..).trans rfl

end DosenPetric.Reduced.Gentzen.BlockedSource
