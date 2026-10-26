module

public import DosenPetric.GentzenMaskLogicalNaturality
public import DosenPetric.GentzenUnaryCasts

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.Route
universe u
variable {P : Type u}

/-- Move a specified whole-formula block past the terminal fixed context. -/
def moveEnd (Γ M Θ : List (NormalForm P)) : Route ((Γ++Θ)++M) (Γ++(M++Θ)) :=
  (Route.exchange Γ M Θ []).cast
    (List.append_nil ((Γ++Θ)++M))
    ((List.append_nil ((Γ++M)++Θ)).trans (List.append_assoc Γ M Θ))

theorem moveEnd_index (Γ M Θ : List (NormalForm P)) {A : NormalForm P}
    (a : At (Γ++(M++Θ)) A) :
    ((moveEnd Γ M Θ).get a).index=exchangeIndex Γ.length M.length Θ.length a.index := by
  rw [moveEnd,Route.get_index_cast,Route.exchange_get,swapBlocks_index,At.index_cast]

theorem moveEnd_before (Γ M Θ : List (NormalForm P)) {A : NormalForm P} (a : At Γ A) :
    (moveEnd Γ M Θ).get (a.before (M++Θ))=(a.before Θ).before M := by
  apply At.index_injective
  rw [moveEnd_index,At.index_before,At.index_before,At.index_before]
  unfold exchangeIndex
  exact ite_eq_left a.index_lt

theorem moveEnd_middle (Γ M Θ : List (NormalForm P)) {A : NormalForm P} (a : At M A) :
    (moveEnd Γ M Θ).get (At.shift Γ (a.before Θ))=At.shift (Γ++Θ) a := by
  apply At.index_injective
  rw [moveEnd_index,At.index_shift,At.index_before,At.index_shift]
  have ha:=a.index_lt
  simp only [List.length_append]
  unfold exchangeIndex
  rw [ite_eq_right (by omega),ite_eq_left (by omega)]
  omega

theorem moveEnd_tail (Γ M Θ : List (NormalForm P)) {A : NormalForm P} (a : At Θ A) :
    (moveEnd Γ M Θ).get (At.shift Γ (At.shift M a))=(At.shift Γ a).before M := by
  apply At.index_injective
  rw [moveEnd_index,At.index_shift,At.index_shift,At.index_before,At.index_shift]
  have ha:=a.index_lt
  unfold exchangeIndex
  rw [ite_eq_right (by omega),ite_eq_right (by omega),ite_eq_left (by omega)]
  omega
end DosenPetric.Reduced.Gentzen.Route
