module

public import DosenPetric.GentzenTerminalLogicalRanks

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.Route
universe u
variable {P : Type u}

theorem rotations_head (o : Op) (F : List (NormalForm P)) (A : NormalForm P) :
    (side P o).comp ((toHead F A).sideArrow o) ((toTail F A).sideArrow o)=
      (side P o).id (fold o (A::F)) := by
  let C:=side P o
  apply side_ext o
  intro B a
  rw [C.assoc,sideArrow_get,sideArrow_get,C.id_comp]
  cases a with
  | here => rw [toTail_here,toHead_last]
  | there a => rw [toTail_there,toHead_before]

theorem rotations_tail (o : Op) (F : List (NormalForm P)) (A : NormalForm P) :
    (side P o).comp ((toTail F A).sideArrow o) ((toHead F A).sideArrow o)=
      (side P o).id (fold o (F++[A])) := by
  let C:=side P o
  apply side_ext o
  intro B a
  rw [C.assoc,sideArrow_get,sideArrow_get,C.id_comp]
  cases At.cases_append F [A] a with
  | inl h => obtain ⟨a,rfl⟩:=h; rw [toHead_before,toTail_there]
  | inr h =>
    obtain ⟨a,rfl⟩:=h
    cases a with
    | here => rw [toHead_last,toTail_here]
    | there a => cases a
end Route

namespace BlockedSource
universe u
variable {P : Type u}

theorem headL_denote {F Δ : List (NormalForm P)} (A : NormalForm P) (f : G P (F++[A]) Δ) :
    ofTerm (headL A f).denote=comp (ofTerm (Route.toHead F A).product) (ofTerm f.denote) :=
  UnaryCast.exchangeL_denote [] F [A] []
    (by simp only [List.nil_append,List.append_nil])
    (by simp only [List.nil_append,List.singleton_append,List.append_nil]) Δ f

theorem tailL_denote {F Δ : List (NormalForm P)} (A : NormalForm P) (f : G P (A::F) Δ) :
    ofTerm (tailL A f).denote=comp (ofTerm (Route.toTail F A).product) (ofTerm f.denote) :=
  UnaryCast.exchangeL_denote [] [A] F []
    (by simp only [List.nil_append,List.singleton_append,List.append_nil])
    (by simp only [List.nil_append,List.append_nil]) Δ f

theorem head_tail_denote {F Δ : List (NormalForm P)} (A : NormalForm P) (f : G P (A::F) Δ) :
    ofTerm (headL A (tailL A f)).denote=ofTerm f.denote := by
  rw [headL_denote,tailL_denote,←Laws.assoc]
  have h:=Route.rotations_head .conj F A
  change comp (ofTerm (Route.toHead F A).product) (ofTerm (Route.toTail F A).product)=id (ante (A::F)) at h
  rw [h,Laws.id_comp]

theorem disjLLast_native {F U Δ Λ : List (NormalForm P)} {A B : NormalForm P}
    (f : G P (A::F) Δ) (g : G P (B::U) Λ) :
    ofTerm (disjLLast (tailL A f) (tailL B g)).denote=
      comp (ofTerm (Route.toTail (F++U) (.disj A B)).product) (ofTerm (G.disjL f g).denote) := by
  rw [disjLLast_eq,tailL_denote]
  exact congrArg (comp (ofTerm (Route.toTail (F++U) (.disj A B)).product))
    (Rules.disjLeft_congr (head_tail_denote A f) (head_tail_denote B g))

end BlockedSource
end DosenPetric.Reduced.Gentzen
