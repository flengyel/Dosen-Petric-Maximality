module

public import DosenPetric.ReducedUnionOccurrences

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced
universe u
variable {P : Type u}

/-- Finite union in an inhabited hom-set. The empty union uses its explicit witness. -/
def finiteUnion {A B : NormalForm P} (w : Hom A B) : List (Hom A B) → Hom A B
  | [] => zeroOf w
  | f :: fs => union f (finiteUnion w fs)

namespace finiteUnion
variable {A B : NormalForm P}

theorem witness_independent (w v : Hom A B) (fs : List (Hom A B)) :
    finiteUnion w fs = finiteUnion v fs := by
  induction fs with
  | nil => exact zeroOf_independent w v
  | cons f fs ih => exact congrArg (union f) ih

theorem singleton (w f : Hom A B) : finiteUnion w [f] = f := union_zeroOf f w

theorem append (w : Hom A B) (fs gs : List (Hom A B)) :
    finiteUnion w (fs ++ gs) = union (finiteUnion w fs) (finiteUnion w gs) := by
  induction fs with
  | nil => exact (zeroOf_union _ w).symm
  | cons f fs ih =>
    change union f (finiteUnion w (fs ++ gs)) = _
    rw [ih,← union_assoc]
    rfl

theorem member_absorb (w : Hom A B) (fs : List (Hom A B)) (f : Hom A B)
    (hf : f ∈ fs) : union f (finiteUnion w fs) = finiteUnion w fs := by
  induction fs with
  | nil => cases hf
  | cons g gs ih =>
    cases List.mem_cons.mp hf with
    | inl h => cases h; exact (union_assoc f f _).symm.trans (congrArg (fun h => union h _) (union_idem f))
    | inr h =>
      change union f (union g (finiteUnion w gs)) = _
      rw [← union_assoc,union_comm f g,union_assoc,ih h]
      rfl

theorem absorb_of_members (w : Hom A B) (fs : List (Hom A B)) (h : Hom A B)
    (hh : ∀ f ∈ fs, union f h = h) : union (finiteUnion w fs) h = h := by
  induction fs with
  | nil => exact zeroOf_union h w
  | cons f fs ih =>
    change union (union f (finiteUnion w fs)) h = h
    rw [union_assoc,ih (fun g hg => hh g (List.mem_cons_of_mem f hg)),hh f (List.mem_cons_self ..)]

/-- Order and repeated summands are irrelevant; the original tags of summands remain. -/
theorem eq_of_members (w v : Hom A B) (fs gs : List (Hom A B))
    (h : ∀ f, f ∈ fs ↔ f ∈ gs) : finiteUnion w fs = finiteUnion v gs := by
  have hfg := absorb_of_members w fs (finiteUnion v gs)
    (fun f hf => member_absorb v gs f ((h f).mp hf))
  have hgf := absorb_of_members v gs (finiteUnion w fs)
    (fun f hf => member_absorb w fs f ((h f).mpr hf))
  exact hgf.symm.trans ((union_comm _ _).trans hfg)

theorem pre {X : NormalForm P} (h : Hom X A) (w : Hom A B) (fs : List (Hom A B)) :
    comp h (finiteUnion w fs) = finiteUnion (comp h w) (fs.map (comp h)) := by
  induction fs with
  | nil => exact zeroOf_pre h w
  | cons f fs ih =>
    change comp h (union f (finiteUnion w fs)) = _
    rw [union_pre,ih]
    rfl

theorem post {Y : NormalForm P} (w : Hom A B) (fs : List (Hom A B)) (h : Hom B Y) :
    comp (finiteUnion w fs) h = finiteUnion (comp w h) (fs.map (fun f => comp f h)) := by
  induction fs with
  | nil => exact zeroOf_post w h
  | cons f fs ih =>
    change comp (union f (finiteUnion w fs)) h = _
    rw [union_post,ih]
    rfl

theorem occurrence (w : Hom A B) (fs : List (Hom A B))
    (x : A.formula.Occ) (y : B.formula.Occ) :
    occurrenceMap (finiteUnion w fs) x y ↔ ∃ f ∈ fs, occurrenceMap f x y := by
  induction fs with
  | nil => simp only [finiteUnion,occurrence_zeroOf,Relations.empty,List.not_mem_nil,false_and,exists_false]
  | cons f fs ih =>
    simp only [finiteUnion,occurrence_union,ih,List.mem_cons]
    constructor
    · intro h
      cases h with
      | inl hf => exact ⟨f,Or.inl rfl,hf⟩
      | inr hg => obtain ⟨g,hg,hr⟩ := hg; exact ⟨g,Or.inr hg,hr⟩
    · rintro ⟨g,hg,hr⟩
      cases hg with
      | inl hg => cases hg; exact Or.inl hr
      | inr hg => exact Or.inr ⟨g,hg,hr⟩

end finiteUnion
end DosenPetric.Reduced
