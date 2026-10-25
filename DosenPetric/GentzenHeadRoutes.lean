module

public import DosenPetric.GentzenLogicalSelectionComponents
public import DosenPetric.GentzenMixedThinning

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.Route
universe u
variable {P : Type u} {F K U L : List (NormalForm P)}

def head (A : NormalForm P) (p : Route K F) : Route (A::K) (A::F) :=
  .cons (.here A K) (p.map At.there)

theorem head_here (A : NormalForm P) (p : Route K F) :
    (p.head A).get (.here A F)=.here A K := rfl

theorem head_there (A : NormalForm P) (p : Route K F) {B : NormalForm P} (a : At F B) :
    (p.head A).get (.there a)=.there (p.get a) := by simp only [head,get,get_map]

theorem head_side (o : Op) (A : NormalForm P) (p : Route K F) :
    (p.head A).sideArrow o=(sideM P o).tensor ((side P o).id A) (p.sideArrow o) := by
  let C:=side P o
  let D:=sideD P o
  apply side_ext o
  intro B a
  cases a with
  | here =>
    rw [sideArrow_get,head_here,component_here,component_here,←D.fst_nat,C.comp_id]
  | there a =>
    rw [sideArrow_get,head_there,component_there,component_there,
      ←C.assoc,←D.snd_nat,C.assoc,sideArrow_get]

/-- Context naturality in the actual native disjunction-left definition. -/
theorem head_disjLeft {Δ Λ : List (NormalForm P)} {A B : NormalForm P}
    (p : Route K F) (q : Route L U)
    (f : Term P (ante (A::F)) (succ Δ)) (g : Term P (ante (B::U)) (succ Λ)) :
    comp (ofTerm ((p.parallel q).head (.disj A B)).product) (ofTerm (Rules.disjLeft f g)) =
      ofTerm (Rules.disjLeft (.comp (p.head A).product f) (.comp (q.head B).product g)) := by
  have hs := parallel_split .conj p q
  have hp := head_side .conj A p
  have hq := head_side .conj B q
  have hh := head_side .conj (.disj A B) (p.parallel q)
  change ofTerm ((p.parallel q).head (.disj A B)).product =
    tensor .conj (id (.disj A B)) (ofTerm (p.parallel q).product) at hh
  change ofTerm (p.head A).product=tensor .conj (id A) (ofTerm p.product) at hp
  change ofTerm (q.head B).product=tensor .conj (id B) (ofTerm q.product) at hq
  change comp (ofTerm (p.parallel q).product) (ofTerm (Gentzen.append .conj F U).invTerm) =
    comp (ofTerm (Gentzen.append .conj K L).invTerm)
      (tensor .conj (ofTerm p.product) (ofTerm q.product)) at hs
  simp only [Rules.disjLeft,ofTerm_comp,ofTerm_tensor,ofTerm_id,term_swap]
  rw [hh,←Laws.assoc (tensor .conj _ _),Laws.tensor_comp,Laws.id_comp,hs,tensor_factor]
  simp only [Laws.assoc]
  rw [←Laws.assoc (tensor .conj (id (.disj A B)) (tensor .conj _ _)),←Laws.swap_nat]
  simp only [Laws.assoc]
  have hn := sourceConj_nat (ofTerm p.product) (ofTerm q.product) (id A) (id B)
  rw [Laws.tensor_id] at hn
  rw [←Laws.assoc (tensor .conj (tensor .conj _ _) _),←hn]
  simp only [Laws.assoc]
  rw [←Laws.assoc (tensor .disj (tensor .conj _ _) (tensor .conj _ _)),
    Laws.tensor_comp,←Laws.swap_nat,←Laws.swap_nat]
  rw [hp,hq,←Laws.tensor_comp]
  simp only [Laws.assoc]
  rw [←Laws.assoc (tensor .disj (tensor .conj _ _) (tensor .conj _ _)),Laws.tensor_comp]

end DosenPetric.Reduced.Gentzen.Route
