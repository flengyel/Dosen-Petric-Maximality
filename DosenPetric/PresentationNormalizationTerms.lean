module

public import DosenPetric.PresentationNegationNaturality

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Presentation.NegationNormalization
universe u
variable {P : Type u}

/-- Raw source representative of the forward normalization comparison. -/
def forwardTerm : (A : Formula P) → (s : Bool) → Term P (source A s) (form A s).formula
  | .var p, false => .id (.var p)
  | .var p, true => .id (.neg (.var p))
  | .top, false => .id .top
  | .top, true => .negTopOut
  | .bot, false => .id .bot
  | .bot, true => .negBotOut
  | .conj A B, false => .tensor .conj (forwardTerm A false) (forwardTerm B false)
  | .conj A B, true => .comp (.dmConjOut A B) (.tensor .disj (forwardTerm A true) (forwardTerm B true))
  | .disj A B, false => .tensor .disj (forwardTerm A false) (forwardTerm B false)
  | .disj A B, true => .comp (.dmDisjOut A B) (.tensor .conj (forwardTerm A true) (forwardTerm B true))
  | .neg A, false => forwardTerm A true
  | .neg A, true => .comp (.dnOut A) (forwardTerm A false)

/-- Raw source representative of the inverse normalization comparison. -/
def backwardTerm : (A : Formula P) → (s : Bool) → Term P (form A s).formula (source A s)
  | .var p, false => .id (.var p)
  | .var p, true => .id (.neg (.var p))
  | .top, false => .id .top
  | .top, true => .negTopIn
  | .bot, false => .id .bot
  | .bot, true => .negBotIn
  | .conj A B, false => .tensor .conj (backwardTerm A false) (backwardTerm B false)
  | .conj A B, true => .comp (.tensor .disj (backwardTerm A true) (backwardTerm B true)) (.dmConjIn A B)
  | .disj A B, false => .tensor .disj (backwardTerm A false) (backwardTerm B false)
  | .disj A B, true => .comp (.tensor .conj (backwardTerm A true) (backwardTerm B true)) (.dmDisjIn A B)
  | .neg A, false => backwardTerm A true
  | .neg A, true => .comp (backwardTerm A false) (.dnIn A)

theorem forwardTerm_denotes (A : Formula P) (s : Bool) :
    ofTerm (forwardTerm A s) = (comparison A s).forward := by
  induction A generalizing s with
  | var p => cases s <;> rfl
  | top => cases s <;> rfl
  | bot => cases s <;> rfl
  | conj A B ih ih' =>
    cases s
    · change tensor .conj (ofTerm (forwardTerm A false)) (ofTerm (forwardTerm B false)) = _
      rw [ih,ih']; rfl
    · change comp (dmConjOut A B) (tensor .disj (ofTerm (forwardTerm A true)) (ofTerm (forwardTerm B true))) = _
      rw [ih,ih']; rfl
  | disj A B ih ih' =>
    cases s
    · change tensor .disj (ofTerm (forwardTerm A false)) (ofTerm (forwardTerm B false)) = _
      rw [ih,ih']; rfl
    · change comp (dmDisjOut A B) (tensor .conj (ofTerm (forwardTerm A true)) (ofTerm (forwardTerm B true))) = _
      rw [ih,ih']; rfl
  | neg A ih =>
    cases s
    · exact ih true
    · change comp (dnOut A) (ofTerm (forwardTerm A false)) = _
      rw [ih]; rfl

theorem backwardTerm_denotes (A : Formula P) (s : Bool) :
    ofTerm (backwardTerm A s) = (comparison A s).backward := by
  induction A generalizing s with
  | var p => cases s <;> rfl
  | top => cases s <;> rfl
  | bot => cases s <;> rfl
  | conj A B ih ih' =>
    cases s
    · change tensor .conj (ofTerm (backwardTerm A false)) (ofTerm (backwardTerm B false)) = _
      rw [ih,ih']; rfl
    · change comp (tensor .disj (ofTerm (backwardTerm A true)) (ofTerm (backwardTerm B true))) (dmConjIn A B) = _
      rw [ih,ih']; rfl
  | disj A B ih ih' =>
    cases s
    · change tensor .disj (ofTerm (backwardTerm A false)) (ofTerm (backwardTerm B false)) = _
      rw [ih,ih']; rfl
    · change comp (tensor .conj (ofTerm (backwardTerm A true)) (ofTerm (backwardTerm B true))) (dmDisjIn A B) = _
      rw [ih,ih']; rfl
  | neg A ih =>
    cases s
    · exact ih true
    · change comp (ofTerm (backwardTerm A false)) (dnIn A) = _
      rw [ih]; rfl

end DosenPetric.Presentation.NegationNormalization
