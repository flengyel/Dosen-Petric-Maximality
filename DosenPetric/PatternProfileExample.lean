module

public import DosenPetric.PatternSubstitutionProfiles

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.PatternProfiles.Example

/-- p=0, q=1; each inserted pattern has its own two local placeholders. -/
def outer : Formula (Fin 2) := .conj (.var 1) (.disj (.var 0) (.var 1))
def first : Formula (Fin 2) := .conj (.var 0) (.var 1)
def second : Formula (Fin 2) := .conj (.var 1) (.disj (.var 0) (.var 1))
def inserted (i : Fin 2) : Formula (Fin 2) := if i.val=0 then first else second

def profiles : ProfileComposition.Data 3 2 := data outer inserted

theorem outer_profile : outer.profile (0 : Fin 3)=1 ∧ outer.profile (1 : Fin 3)=0 ∧ outer.profile (2 : Fin 3)=1 :=
  ⟨rfl,rfl,rfl⟩
theorem first_profile : first.profile (0 : Fin 2)=0 ∧ first.profile (1 : Fin 2)=1 := ⟨rfl,rfl⟩
theorem second_profile : second.profile (0 : Fin 3)=1 ∧ second.profile (1 : Fin 3)=0 ∧ second.profile (2 : Fin 3)=1 :=
  ⟨rfl,rfl,rfl⟩

theorem source_sizes : profiles.n (profiles.outer 0)=3 ∧
    profiles.n (profiles.outer 1)=2 ∧ profiles.n (profiles.outer 2)=3 := ⟨rfl,rfl,rfl⟩

def delta (i : Fin 8) : Fin 4 := profiles.delta i

theorem eight_positions :
    [(delta 0).val+1,(delta 1).val+1,(delta 2).val+1,(delta 3).val+1,
     (delta 4).val+1,(delta 5).val+1,(delta 6).val+1,(delta 7).val+1] =
    [4,3,4,1,2,4,3,4] := rfl

theorem source_position_two :
    FiniteBlocks.decode (fun r => profiles.n (profiles.outer r)) (1 : Fin 8) = ⟨0,(1 : Fin 3)⟩ := rfl

theorem gamma_position_two : profiles.gamma ⟨0,(1 : Fin 3)⟩ = profiles.b 1 (0 : Fin 2) := rfl

theorem target_encoding_three : (FiniteBlocks.encode profiles.l (profiles.b 1 (0 : Fin 2))).val+1=3 := rfl

/-- The printed delta(2)=3, translated from zero-based Fin indices. -/
theorem delta_two : (delta 1).val+1=3 := rfl

/-- Local names may all coincide without collapsing either occurrence tag. -/
theorem noninjective_renaming :
    (outer.subst (insertion inserted)).rename (fun _ => ()) =
      outer.subst (fun i => (insertion inserted i).rename (fun _ => ())) :=
  renaming_square outer inserted (fun _ => ())

end DosenPetric.PatternProfiles.Example
