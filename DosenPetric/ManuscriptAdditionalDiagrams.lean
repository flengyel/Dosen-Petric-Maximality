module

public import DosenPetric.ManuscriptFinalConsequences

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric
universe u v
namespace Structure
variable {P : Type u} {C : Category.{u,v} (Formula P)} (S : Structure C)

/-- The actual product/coproduct rectangle used to retract a contextual equation. -/
theorem context_retract_square {A B : Formula P} (m : C.Hom A B) (n : C.Hom B A)
    (hmn : C.comp m n = C.id A) :
    C.comp (C.comp (S.prodMap m (C.id .bot)) (C.comp (S.fst B .bot) (S.j B)))
      (S.sumMap n (C.id .top)) = C.comp (S.fst A .bot) (S.j A) := by
  dsimp only [prodMap,sumMap,j]
  rw [← C.assoc _ (S.fst B .bot),S.pair_fst,C.assoc,C.assoc,
    S.inl_copair,← C.assoc m n,hmn,C.id_comp]

end Structure
namespace Presentation.ManuscriptSubstitution
variable {P : Type u}

theorem double_negation_square (A : Formula P) :
    comp (comp ((operations P).prodMap ((doubleNegation P).into A) (Presentation.id .bot))
      (context (.neg (.neg A))))
      ((operations P).sumMap ((doubleNegation P).out A) (Presentation.id .top)) = context A :=
  (operations P).context_retract_square ((doubleNegation P).into A)
    ((doubleNegation P).out A) ((doubleNegation P).into_out A)

end Presentation.ManuscriptSubstitution
namespace ProfileComposition.Data
variable {m k : Nat} (S : ProfileComposition.Data m k)

theorem a_disjoint {r r' : Fin m} (h : r ≠ r')
    (t : Fin (S.n (S.outer r))) (t' : Fin (S.n (S.outer r'))) : S.a r t ≠ S.a r' t' := by
  intro he
  exact h (congrArg Sigma.fst he)

theorem b_disjoint {i j : Fin k} (h : i ≠ j)
    (s : Fin (S.l i)) (t : Fin (S.l j)) : S.b i s ≠ S.b j t := by
  intro he
  exact h (congrArg Sigma.fst he)

end ProfileComposition.Data
end DosenPetric
