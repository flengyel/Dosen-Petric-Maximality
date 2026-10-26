module

public import DosenPetric.GentzenMaskCoordinates
public import DosenPetric.GentzenLogicalComponents

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.SelectionMask
universe u
variable {P : Type u} {C : NormalForm P} {Γ Θ : List (NormalForm P)}

theorem allFixed_picked {F : List (NormalForm P)} {A : NormalForm P} (a : At F A) :
    (allFixed (C:=C) F).picked a=false := by
  induction a with
  | here=>rfl
  | there a ih=>exact ih

theorem allFixed_offset {F : List (NormalForm P)} {A : NormalForm P} (a : At F A) :
    (allFixed (C:=C) F).offset a=a.index := by
  induction a with
  | here=>rfl
  | there a ih=>exact congrArg (fun n=>n+1) ih

def contextMask (g : SelectionMask C Γ) (t : SelectionMask C Θ) (M : List (NormalForm P)) :=
  g.append ((allFixed M).append t)

theorem context_erased (g : SelectionMask C Γ) (t : SelectionMask C Θ) (M : List (NormalForm P)) :
    (contextMask g t M).erased=g.erased++(M++t.erased) := by
  rw [contextMask,append_erased,append_erased,allFixed_erased]

def contextCanonical (g : SelectionMask C Γ) (t : SelectionMask C Θ) (M : List (NormalForm P)) :
    Route (C::(g.erased++(M++t.erased))) (Γ++(M++Θ)) :=
  (contextMask g t M).canonical.cast (congrArg (List.cons C) (context_erased g t M)) rfl

theorem contextCanonical_index (g : SelectionMask C Γ) (t : SelectionMask C Θ)
    (M : List (NormalForm P)) {A : NormalForm P} (a : At (Γ++(M++Θ)) A) :
    ((contextCanonical g t M).get a).index=
      if (contextMask g t M).picked a then 0 else (contextMask g t M).offset a+1 := by
  rw [contextCanonical,Route.get_index_cast]
  exact (contextMask g t M).canonical_index a

theorem contextCanonical_before (g : SelectionMask C Γ) (t : SelectionMask C Θ)
    (M : List (NormalForm P)) {A : NormalForm P} (a : At Γ A) :
    ((contextCanonical g t M).get (a.before (M++Θ))).index=
      if g.picked a then 0 else g.offset a+1 := by
  rw [contextCanonical_index]
  simp only [contextMask,append_picked_before,append_offset_before]

theorem contextCanonical_middle (g : SelectionMask C Γ) (t : SelectionMask C Θ)
    (M : List (NormalForm P)) {A : NormalForm P} (a : At M A) :
    ((contextCanonical g t M).get (At.shift Γ (a.before Θ))).index=
      g.erased.length+a.index+1 := by
  rw [contextCanonical_index]
  simp only [contextMask,append_picked_shift,append_picked_before,allFixed_picked,Bool.false_eq_true,ite_false,
    append_offset_shift,append_offset_before,allFixed_offset]

theorem contextCanonical_tail (g : SelectionMask C Γ) (t : SelectionMask C Θ)
    (M : List (NormalForm P)) {A : NormalForm P} (a : At Θ A) :
    ((contextCanonical g t M).get (At.shift Γ (At.shift M a))).index=
      if t.picked a then 0 else g.erased.length+M.length+t.offset a+1 := by
  rw [contextCanonical_index]
  simp only [contextMask,append_picked_shift,append_offset_shift,allFixed_erased,Nat.add_assoc]
end DosenPetric.Reduced.Gentzen.SelectionMask
