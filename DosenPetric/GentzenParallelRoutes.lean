module

public import DosenPetric.GentzenSelectionMerge

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.Route
universe u
variable {P : Type u} {F K U L : List (NormalForm P)}

def parallel (p : Route K F) (q : Route L U) : Route (K++L) (F++U) :=
  (p.map (fun a => a.before L)).append (q.map (At.shift K))

theorem append_before {Γ Δ Θ : List (NormalForm P)} (p : Route Γ Δ) (q : Route Γ Θ)
    {A : NormalForm P} (a : At Δ A) : (p.append q).get (a.before Θ) = p.get a := by
  induction a with
  | here => cases p; rfl
  | there a ih => cases p with | cons b p => exact ih p

theorem append_shift {Γ Δ Θ : List (NormalForm P)} (p : Route Γ Δ) (q : Route Γ Θ)
    {A : NormalForm P} (a : At Θ A) : (p.append q).get (At.shift Δ a) = q.get a := by
  induction p with
  | nil => rfl
  | cons b p ih => exact ih

theorem parallel_before (p : Route K F) (q : Route L U)
    {A : NormalForm P} (a : At F A) : (p.parallel q).get (a.before U) = (p.get a).before L := by
  rw [parallel,append_before,get_map]
theorem parallel_shift (p : Route K F) (q : Route L U)
    {A : NormalForm P} (a : At U A) : (p.parallel q).get (At.shift F a) = At.shift K (q.get a) := by
  rw [parallel,append_shift,get_map]

theorem parallel_join (o : Op) (p : Route K F) (q : Route L U) :
    (side P o).comp (join o K L) ((p.parallel q).sideArrow o) =
      (side P o).comp ((sideM P o).tensor (p.sideArrow o) (q.sideArrow o)) (join o F U) := by
  let C := side P o
  let D := sideD P o
  apply side_ext o
  intro A a
  cases At.cases_append F U a with
  | inl h =>
    obtain ⟨a,rfl⟩ := h
    rw [C.assoc,sideArrow_get,parallel_before,join_before,C.assoc,join_before,
      ←C.assoc,←D.fst_nat,C.assoc,sideArrow_get]
  | inr h =>
    obtain ⟨a,rfl⟩ := h
    rw [C.assoc,sideArrow_get,parallel_shift,join_shift,C.assoc,join_shift,
      ←C.assoc,←D.snd_nat,C.assoc,sideArrow_get]

theorem parallel_split (o : Op) (p : Route K F) (q : Route L U) :
    (side P o).comp ((p.parallel q).sideArrow o) (split o F U) =
      (side P o).comp (split o K L) ((sideM P o).tensor (p.sideArrow o) (q.sideArrow o)) := by
  let C := side P o
  apply DiagonalData.cancel_left (C:=C) _ _ (join o K L) (split o K L) (split_join o K L)
  rw [←C.assoc,parallel_join,C.assoc,join_split,C.comp_id,←C.assoc,join_split,C.id_comp]

end DosenPetric.Reduced.Gentzen.Route
