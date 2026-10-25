module

public import DosenPetric.GentzenHeadRoutes
public import DosenPetric.GentzenMixedInjections

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.Route
universe u
variable {P : Type u} {F K U L Δ Λ : List (NormalForm P)} {A B : NormalForm P}

theorem head_conjRight (p : Route K F) (q : Route L U)
    (f : Term P (ante Δ) (succ (A::F))) (g : Term P (ante Λ) (succ (B::U))) :
    comp (ofTerm (Rules.conjRight f g)) (ofTerm ((p.parallel q).head (.conj A B)).coproduct) =
      ofTerm (Rules.conjRight (.comp f (p.head A).coproduct) (.comp g (q.head B).coproduct)) := by
  have hs:=parallel_split .disj p q
  have hp:=head_side .disj A p
  have hq:=head_side .disj B q
  have hh:=head_side .disj (.conj A B) (p.parallel q)
  change ofTerm (p.head A).coproduct=tensor .disj (id A) (ofTerm p.coproduct) at hp
  change ofTerm (q.head B).coproduct=tensor .disj (id B) (ofTerm q.coproduct) at hq
  change ofTerm ((p.parallel q).head (.conj A B)).coproduct=
    tensor .disj (id (.conj A B)) (ofTerm (p.parallel q).coproduct) at hh
  change comp (ofTerm (Gentzen.append .disj F U).toTerm) (ofTerm (p.parallel q).coproduct)=
    comp (tensor .disj (ofTerm p.coproduct) (ofTerm q.coproduct))
      (ofTerm (Gentzen.append .disj K L).toTerm) at hs
  simp only [Rules.conjRight,ofTerm_comp,ofTerm_tensor,ofTerm_id]
  rw [hh,Laws.assoc,Laws.assoc,Laws.assoc,Laws.tensor_comp,Laws.id_comp,hs,tensor_factor]
  have hn:=mixedDisj_nat (id A) (ofTerm p.coproduct) (id B) (ofTerm q.coproduct)
  rw [Laws.tensor_id] at hn
  rw [←Laws.assoc (ofTerm (Term.mixedDisj A (succ F) B (succ U))),hn]
  simp only [Laws.assoc]
  rw [hp,hq,←Laws.tensor_comp]
  simp only [Laws.assoc]

end DosenPetric.Reduced.Gentzen.Route
