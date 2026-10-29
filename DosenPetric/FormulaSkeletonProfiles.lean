module

public import DosenPetric.FormulaRenamingCoordinates

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Formula
universe u v
variable {P : Type u}

/-- Erase placeholder names to one common symbol, retaining the entire syntax. -/
def skeleton (A : Formula P) : Formula Unit := A.rename (fun _ => ())

theorem skeleton_rename {Q : Type v} (ρ : P → Q) (A : Formula P) : (A.rename ρ).skeleton = A.skeleton := by
  change (A.subst (fun p => .var (ρ p))).subst (fun _ => .var ()) = A.subst (fun _ => .var ())
  rw [subst_composition]
  rfl

/-- Restore one label at each tagged occurrence of a skeleton. -/
def decorate : (S : Formula Unit) → (S.Occ → P) → Formula P
  | .var _,f => .var (f ())
  | .top,_ => .top
  | .bot,_ => .bot
  | .conj A B,f => .conj (decorate A (fun x => f (.inl x))) (decorate B (fun x => f (.inr x)))
  | .disj A B,f => .disj (decorate A (fun x => f (.inl x))) (decorate B (fun x => f (.inr x)))
  | .neg A,f => .neg (decorate A f)

theorem decorate_skeleton (A : Formula P) :
    decorate A.skeleton (fun x => A.label (A.unrenameOcc (fun _ => ()) x)) = A := by
  induction A with
  | var p => rfl
  | top => rfl
  | bot => rfl
  | conj A B ih ih' => exact congrArgTwo Formula.conj ih ih'
  | disj A B ih ih' => exact congrArgTwo Formula.disj ih ih'
  | neg A ih => exact congrArg Formula.neg ih

/-- The usual finite profile, transported along the proved count preservation. -/
def skeletonProfile (A : Formula P) (i : Fin A.skeleton.occurrenceCount) : P :=
  A.profile (Fin.cast (A.rename_count (fun _ => ())) i)

def fromSkeletonProfile (S : Formula Unit) (o : Fin S.occurrenceCount → P) : Formula P :=
  decorate S (fun x => o (S.occurrenceIndex x))

theorem skeletonProfile_position (A : Formula P) (x : A.skeleton.Occ) :
    A.skeletonProfile (A.skeleton.occurrenceIndex x) = A.label (A.unrenameOcc (fun _ => ()) x) := by
  have hi : Fin.cast (A.rename_count (fun _ => ())) (A.skeleton.occurrenceIndex x) =
      A.occurrenceIndex (A.unrenameOcc (fun _ => ()) x) := by
    apply Fin.ext
    have he := A.rename_index_value (fun _ => ()) (A.unrenameOcc (fun _ => ()) x)
    rw [rename_unrename] at he
    exact he
  unfold skeletonProfile
  rw [hi,profile_index]

theorem skeleton_profile_reconstruction (A : Formula P) :
    fromSkeletonProfile A.skeleton A.skeletonProfile = A := by
  unfold fromSkeletonProfile
  have he : (fun x => A.skeletonProfile (A.skeleton.occurrenceIndex x)) =
      (fun x => A.label (A.unrenameOcc (fun _ => ()) x)) := funext (skeletonProfile_position A)
  rw [he]
  exact decorate_skeleton A

theorem fromSkeletonProfile_heq {S S' : Formula Unit} (h : S = S')
    {o : Fin S.occurrenceCount → P} {o' : Fin S'.occurrenceCount → P} (ho : HEq o o') :
    HEq (fromSkeletonProfile S o) (fromSkeletonProfile S' o') := by
  cases h
  cases eq_of_heq ho
  rfl

/-- A skeleton and its profile determine the complete formula pattern. -/
theorem skeleton_profile_unique (A B : Formula P) (h : A.skeleton = B.skeleton)
    (ho : HEq A.skeletonProfile B.skeletonProfile) : A = B := by
  have he := fromSkeletonProfile_heq h ho
  rw [skeleton_profile_reconstruction,skeleton_profile_reconstruction] at he
  exact eq_of_heq he

end DosenPetric.Formula
