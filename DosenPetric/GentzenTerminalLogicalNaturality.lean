module

public import DosenPetric.GentzenRotationRoutes

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace Rules

def terminalDisjLeft {F U Δ Λ : List (NormalForm P)} {A B : NormalForm P}
    (f : Term P (ante (F++[A])) (succ Δ)) (g : Term P (ante (U++[B])) (succ Λ)) :
    Term P (ante ((F++U)++[.disj A B])) (succ (Δ++Λ)) :=
  .comp (Route.toTail (F++U) (.disj A B)).product
    (disjLeft (.comp (Route.toHead F A).product f) (.comp (Route.toHead U B).product g))

/-- The three exchanges in the source macro are retained in this comparison. -/
theorem terminalDisjLeft_denote {F U Δ Λ : List (NormalForm P)} {A B : NormalForm P}
    (f : G P (F++[A]) Δ) (g : G P (U++[B]) Λ) :
    ofTerm (BlockedSource.disjLLast f g).denote = ofTerm (terminalDisjLeft f.denote g.denote) := by
  let f' : G P (A::F) Δ := UnaryCast.exchangeL [] F [A] []
    (by simp only [List.nil_append,List.append_nil])
    (by simp only [List.nil_append,List.singleton_append,List.append_nil]) Δ f
  let g' : G P (B::U) Λ := UnaryCast.exchangeL [] U [B] []
    (by simp only [List.nil_append,List.append_nil])
    (by simp only [List.nil_append,List.singleton_append,List.append_nil]) Λ g
  have he : BlockedSource.disjLLast f g = UnaryCast.exchangeL [] [.disj A B] (F++U) []
      (by simp only [List.nil_append,List.singleton_append,List.append_nil])
      (by simp only [List.nil_append,List.append_nil]) (Δ++Λ) (G.disjL f' g') := rfl
  rw [he,UnaryCast.exchangeL_denote]
  change comp (ofTerm (Route.toTail (F++U) (.disj A B)).product)
    (ofTerm (Rules.disjLeft f'.denote g'.denote)) = _
  simp only [terminalDisjLeft,Rules.disjLeft,ofTerm_comp,ofTerm_tensor]
  have hf := UnaryCast.exchangeL_denote (U:=A::F) [] F [A] []
    (by simp only [List.nil_append,List.append_nil])
    (by simp only [List.nil_append,List.singleton_append,List.append_nil]) Δ f
  have hg := UnaryCast.exchangeL_denote (U:=B::U) [] U [B] []
    (by simp only [List.nil_append,List.append_nil])
    (by simp only [List.nil_append,List.singleton_append,List.append_nil]) Λ g
  change ofTerm f'.denote=comp (ofTerm (Route.toHead F A).product) (ofTerm f.denote) at hf
  change ofTerm g'.denote=comp (ofTerm (Route.toHead U B).product) (ofTerm g.denote) at hg
  rw [hf,hg]

theorem terminalDisjLeft_nat {F K U L Δ Λ : List (NormalForm P)} {A B : NormalForm P}
    (p : Route K F) (q : Route L U)
    (f : Term P (ante (F++[A])) (succ Δ)) (g : Term P (ante (U++[B])) (succ Λ)) :
    comp (ofTerm ((p.parallel q).parallel (Route.identity [.disj A B])).product)
      (ofTerm (terminalDisjLeft f g)) =
    ofTerm (terminalDisjLeft (.comp (p.parallel (Route.identity [A])).product f)
      (.comp (q.parallel (Route.identity [B])).product g)) := by
  have ht := Route.tail_rotation .conj (.disj A B) (p.parallel q)
  have hp := Route.head_rotation .conj A p
  have hq := Route.head_rotation .conj B q
  change comp (ofTerm ((p.parallel q).parallel (Route.identity [.disj A B])).product)
      (ofTerm (Route.toTail (F++U) (.disj A B)).product) =
    comp (ofTerm (Route.toTail (K++L) (.disj A B)).product)
      (ofTerm ((p.parallel q).head (.disj A B)).product) at ht
  change comp (ofTerm (p.head A).product) (ofTerm (Route.toHead F A).product) =
    comp (ofTerm (Route.toHead K A).product) (ofTerm (p.parallel (Route.identity [A])).product) at hp
  change comp (ofTerm (q.head B).product) (ofTerm (Route.toHead U B).product) =
    comp (ofTerm (Route.toHead L B).product) (ofTerm (q.parallel (Route.identity [B])).product) at hq
  simp only [terminalDisjLeft,ofTerm_comp]
  rw [←Laws.assoc,ht,Laws.assoc,Route.head_disjLeft]
  simp only [Rules.disjLeft,ofTerm_comp,ofTerm_tensor]
  rw [←Laws.assoc (ofTerm (p.head A).product),hp,Laws.assoc,
    ←Laws.assoc (ofTerm (q.head B).product),hq,Laws.assoc]

end Rules
end DosenPetric.Reduced.Gentzen
