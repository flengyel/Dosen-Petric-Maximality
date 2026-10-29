module

public import DosenPetric.GentzenBlockedDisjFirstRank

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.BlockedDisjFirst
universe u
variable {P : Type u}

/-- The source's right rank is the selected antecedent rank in the right cut premise. -/
theorem fresh_principal_rank {A B : NormalForm P} {X Y Z D E I R : List (NormalForm P)}
    (g : G P (Z++[B]) E) (k : G P (A::((parametric A B X Y).erase++I)) (D++R)) :
    (SequentialDisjFirst.fresh k (SequentialDisjFirst.secondChild g)).rho .left
      (.here (.disj A B) (((parametric A B X Y).erase++I)++Z)) = 1 :=
  G.rho_disjL_principal k (SequentialDisjFirst.secondChild g)

theorem fresh_total_rank {A B : NormalForm P} {X Y Z D E I J : List (NormalForm P)}
    (g : G P (Z++[B]) E) (h : G P I J) (z : At J (.disj A B))
    (k : G P (A::((parametric A B X Y).erase++I)) (D++z.erase)) :
    PositionalCut.rank h z (SequentialDisjFirst.fresh k (SequentialDisjFirst.secondChild g))
      (.here (.disj A B) (((parametric A B X Y).erase++I)++Z)) = h.rho .right z+1 :=
  PositionalCut.rank_fresh_disjL h z k (SequentialDisjFirst.secondChild g)

theorem fresh_total_rank_ge_two {A B : NormalForm P} {X Y Z D E I J : List (NormalForm P)}
    (g : G P (Z++[B]) E) (h : G P I J) (z : At J (.disj A B))
    (k : G P (A::((parametric A B X Y).erase++I)) (D++z.erase)) :
    2 ≤ PositionalCut.rank h z (SequentialDisjFirst.fresh k (SequentialDisjFirst.secondChild g))
      (.here (.disj A B) (((parametric A B X Y).erase++I)++Z)) :=
  PositionalCut.rank_ge_two h z _ _

end DosenPetric.Reduced.Gentzen.BlockedDisjFirst
