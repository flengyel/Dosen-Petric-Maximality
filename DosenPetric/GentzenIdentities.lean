module

public import DosenPetric.GentzenRoutingLaws
public import DosenPetric.GentzenDerived

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.G
universe u
variable {P : Type u}

def topIdentity : G P [.top] [.top] := .thinL [] [] [.top] .top .topI
def botIdentity : G P [.bot] [.bot] := .thinR [.bot] [] [] .bot .botE

def identityNF : (A : NormalForm P) → G P [A] [A]
  | .lit l => .identity l
  | .top => topIdentity
  | .bot => botIdentity
  | .conj A B => (identityNF A).tensorConj (identityNF B)
  | .disj A B => (identityNF A).tensorDisj (identityNF B)

def zeroNF : (A : NormalForm P) → G P [A] [A]
  | .lit l => .zero l
  | .top => topIdentity
  | .bot => botIdentity
  | .conj A B => (zeroNF A).tensorConj (zeroNF B)
  | .disj A B => (zeroNF A).tensorDisj (zeroNF B)

theorem identityNF_value (A : NormalForm P) : decode (identityNF A).denote = id A := by
  induction A with
  | lit l => exact decode_encode (.id (.lit l))
  | top => exact fromTop_unique _ _
  | bot => exact toBot_unique _ _
  | conj A B ih ih' => rw [identityNF, tensorConj_value, ih, ih', Laws.tensor_id]
  | disj A B ih ih' => rw [identityNF, tensorDisj_value, ih, ih', Laws.tensor_id]

theorem zeroNF_value (A : NormalForm P) : decode (zeroNF A).denote = Reduced.zero A := by
  induction A with
  | lit l => exact decode_encode (.zero (.lit l))
  | top => exact fromTop_unique _ _
  | bot => exact toBot_unique _ _
  | conj A B ih ih' => rw [zeroNF, tensorConj_value, ih, ih', tensor_zero]
  | disj A B ih ih' => rw [zeroNF, tensorDisj_value, ih, ih', tensor_zero]

end DosenPetric.Reduced.Gentzen.G
