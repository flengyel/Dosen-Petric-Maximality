module

public import DosenPetric.GentzenBlockedMixCore
public import DosenPetric.GentzenRoutePrograms
public import DosenPetric.GentzenParallelRoutes

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace Route

/-- Split the target of a concatenated positional route into its two parts. -/
theorem append_split (o : Op) {K F U : List (NormalForm P)}
    (p : Route K F) (q : Route K U) :
    (side P o).comp ((p.append q).sideArrow o) (split o F U) =
      (sideD P o).pair (p.sideArrow o) (q.sideArrow o) := by
  let C := side P o
  let D := sideD P o
  have he : (p.append q).sideArrow o =
      C.comp (D.pair (p.sideArrow o) (q.sideArrow o)) (join o F U) := by
    apply side_ext o
    intro A a
    cases At.cases_append F U a with
    | inl h =>
      obtain ⟨a,rfl⟩ := h
      rw [sideArrow_get,append_before,C.assoc,join_before,← C.assoc,D.pair_fst,sideArrow_get]
    | inr h =>
      obtain ⟨a,rfl⟩ := h
      rw [sideArrow_get,append_shift,C.assoc,join_shift,← C.assoc,D.pair_snd,sideArrow_get]
  rw [he,C.assoc,join_split,C.comp_id]

theorem identity_arrow (o : Op) (K : List (NormalForm P)) :
    (identity K).sideArrow o = (side P o).id (fold o K) := by
  apply side_ext o
  intro A a
  rw [sideArrow_get,get_identity,(side P o).id_comp]

/-- Projection onto the first block, with no assumption that it is inhabited. -/
def takeFirst (K L : List (NormalForm P)) : Route (K++L) K :=
  (identity K).map (fun a => a.before L)

/-- Projection onto the second block, including the empty-block cases. -/
def takeSecond (K L : List (NormalForm P)) : Route (K++L) L :=
  (identity L).map (At.shift K)

theorem takeFirst_arrow (o : Op) (K L : List (NormalForm P)) :
    (takeFirst K L).sideArrow o =
      (side P o).comp (split o K L) ((sideD P o).fst (fold o K) (fold o L)) := by
  let C := side P o
  apply side_ext o
  intro A a
  rw [sideArrow_get]
  change component o (((identity K).map (fun a => a.before L)).get a) = _
  rw [get_map,get_identity,C.assoc,← join_before]
  rw [← C.assoc,split_join,C.id_comp]

theorem takeSecond_arrow (o : Op) (K L : List (NormalForm P)) :
    (takeSecond K L).sideArrow o =
      (side P o).comp (split o K L) ((sideD P o).snd (fold o K) (fold o L)) := by
  let C := side P o
  apply side_ext o
  intro A a
  rw [sideArrow_get]
  change component o (((identity L).map (At.shift K)).get a) = _
  rw [get_map,get_identity,C.assoc,← join_shift]
  rw [← C.assoc,split_join,C.id_comp]

end Route
namespace BlockedMix

/-- Both copies of the unchanged cut input are realized by unary rules. -/
def inputRoute {Y F H : List (NormalForm P)} (p : Route Y F) (q : Route Y H)
    (I : List (NormalForm P)) : Route (Y++I) ((H++I)++(F++I)) :=
  (q.parallel (Route.identity I)).append (p.parallel (Route.identity I))

/-- The two residual output copies are contracted after the parallel mix. -/
def outputRoute (D E R : List (NormalForm P)) :
    Route ((E++D)++R) ((E++R)++(D++R)) :=
  ((Route.takeFirst E D).parallel (Route.identity R)).append
    ((Route.takeSecond E D).parallel (Route.identity R))

/-- The native rule receives two cut-free results before either block repair. -/
def parallel {Y F H D E I R : List (NormalForm P)}
    (p : Route Y F) (q : Route Y H)
    (k : G P (F++I) (D++R)) (l : G P (H++I) (E++R)) :
    G P (Y++I) ((E++D)++R) :=
  (inputRoute p q I).program.left ((outputRoute D E R).program.right (G.mix k l))

theorem parallel_count {Y F H D E I R : List (NormalForm P)}
    (p : Route Y F) (q : Route Y H)
    (k : G P (F++I) (D++R)) (l : G P (H++I) (E++R)) :
    (parallel p q k l).cutCount = k.cutCount+l.cutCount := by
  simp only [parallel,StructuralProgram.left_count,StructuralProgram.right_count,G.cutCount]

end BlockedMix
end DosenPetric.Reduced.Gentzen
