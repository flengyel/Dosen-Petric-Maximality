module

public import DosenPetric.DependentCoordinateMaps

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.PatternProfiles
open ProfileComposition
universe u
variable {k : Nat} {l : Fin k → Nat}
  (M : Formula (Fin k)) (N : ∀ i, Formula (Fin (l i)))

def data : Data M.occurrenceCount k where
  outer := M.profile
  n i := (N i).occurrenceCount
  l := l
  inner i := (N i).profile

def tag (i : Fin k) (s : Fin (l i)) : ((i : Fin k) × Fin (l i)) := ⟨i,s⟩

/-- Tag each local placeholder by its own inserted-pattern index. -/
def insertion (i : Fin k) : Formula ((i : Fin k) × Fin (l i)) :=
  (N i).rename (tag i)

/-- A finite pair (r,t) gives the exact old tag and the exact inner occurrence
of the renamed inserted pattern. Its type is the actual Formula.Block. -/
def taggedBlock (z : (data M N).Domain) : M.Block (insertion N) :=
  ⟨M.occurrenceAt z.1,
    (N (M.profile z.1)).renameOcc (tag (M.profile z.1))
      ((N (M.profile z.1)).occurrenceAt z.2)⟩

theorem taggedBlock_injective {x y : (data M N).Domain} (h : taggedBlock M N x = taggedBlock M N y) : x = y := by
  apply DependentCoordinates.sigma_injective
    (F:=fun r : Fin M.occurrenceCount => Fin ((N (M.profile r)).occurrenceCount))
    (G:=fun r : M.Occ => (insertion N (M.label r)).Occ) M.occurrenceAt ?_
    (fun r t => (N (M.profile r)).renameOcc (tag (M.profile r))
      ((N (M.profile r)).occurrenceAt t)) ?_ h
  · intro a b h
    have he := congrArg M.occurrenceIndex h
    rw [Formula.occurrenceIndex_at,Formula.occurrenceIndex_at] at he
    exact he
  · intro r a b h
    have he := Formula.renameOcc_injective _ _ h
    have hi := congrArg (N (M.profile r)).occurrenceIndex he
    rw [Formula.occurrenceIndex_at,Formula.occurrenceIndex_at] at hi
    exact hi

theorem taggedBlock_surjective (x : M.Block (insertion N)) :
    ∃ z : (data M N).Domain, taggedBlock M N z = x := by
  apply DependentCoordinates.sigma_surjective
    (F:=fun r : Fin M.occurrenceCount => Fin ((N (M.profile r)).occurrenceCount))
    (G:=fun r : M.Occ => (insertion N (M.label r)).Occ) M.occurrenceAt ?_
    (fun r t => (N (M.profile r)).renameOcc (tag (M.profile r))
      ((N (M.profile r)).occurrenceAt t)) ?_ x
  · intro r
    exact ⟨M.occurrenceIndex r,M.occurrenceAt_index r⟩
  · intro r t
    refine ⟨(N (M.profile r)).occurrenceIndex ((N (M.profile r)).unrenameOcc _ t),?_⟩
    rw [Formula.occurrenceAt_index]
    exact (N (M.profile r)).rename_unrename (tag (M.profile r)) t

/-- The inverse of the printed chi: rebuild the actual occurrence from (r,t). -/
def chiInverse (z : (data M N).Domain) : (M.subst (insertion N)).Occ :=
  M.contract (insertion N) (taggedBlock M N z)

theorem chiInverse_injective {x y : (data M N).Domain} (h : chiInverse M N x = chiInverse M N y) : x = y :=
  taggedBlock_injective M N (Formula.contract_injective _ M h)

theorem chiInverse_surjective (x : (M.subst (insertion N)).Occ) :
    ∃ z : (data M N).Domain, chiInverse M N z = x := by
  obtain ⟨z,hz⟩ := taggedBlock_surjective M N (M.expand (insertion N) x)
  refine ⟨z,?_⟩
  unfold chiInverse
  rw [hz,Formula.contract_expand]

/-- The unique finite coordinates of an actual substituted occurrence.
The inverse is explicit; choice merely names its proved unique inverse map. -/
noncomputable def chi (x : (M.subst (insertion N)).Occ) : (data M N).Domain :=
  Classical.choose (chiInverse_surjective M N x)

theorem chiInverse_chi (x : (M.subst (insertion N)).Occ) : chiInverse M N (chi M N x) = x :=
  Classical.choose_spec (chiInverse_surjective M N x)

theorem chi_chiInverse (z : (data M N).Domain) : chi M N (chiInverse M N z) = z :=
  chiInverse_injective M N (chiInverse_chi M N (chiInverse M N z))

theorem unique_coordinates (x : (M.subst (insertion N)).Occ) :
    ∃ z : (data M N).Domain, chiInverse M N z = x ∧
      ∀ z', chiInverse M N z' = x → z' = z := by
  refine ⟨chi M N x,chiInverse_chi M N x,?_⟩
  intro z h
  exact chiInverse_injective M N (h.trans (chiInverse_chi M N x).symm)

theorem chiInverse_label (z : (data M N).Domain) :
    (M.subst (insertion N)).label (chiInverse M N z) = (data M N).gamma z := by
  rw [chiInverse,Formula.contract_label]
  exact (N (M.profile z.1)).rename_label (tag (M.profile z.1)) ((N (M.profile z.1)).occurrenceAt z.2)

/-- The actual occurrence-label square in Appendix A, with both finite indices. -/
theorem occurrence_label_square (x : (M.subst (insertion N)).Occ) :
    (data M N).gamma (chi M N x) = (M.subst (insertion N)).label x := by
  rw [← chiInverse_label,chiInverse_chi]

/-- The shared-variable square permits arbitrary, including noninjective, rho. -/
theorem renaming_square {Q : Type u} (ρ : ((i : Fin k) × Fin (l i)) → Q) :
    (M.subst (insertion N)).rename ρ = M.subst (fun i => (insertion N i).rename ρ) :=
  M.rename_substitution (insertion N) ρ

end DosenPetric.PatternProfiles
