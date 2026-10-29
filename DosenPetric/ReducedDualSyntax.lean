module

public import DosenPetric.ReducedReductionFunctor

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced
universe u
variable {P : Type u}

namespace Op
def dual : Op → Op
  | .conj => .disj
  | .disj => .conj
end Op

namespace Term

/-- Typed contravariant reflection of the full reduced grammar. This is a
construction on terms; quotient descent is proved separately. -/
def dual : {A B : NormalForm P} → Term P A B → Term P B.dual A.dual
  | _,_,.id A => .id A.dual
  | _,_,.comp f g => .comp g.dual f.dual
  | _,_,.tensor .conj f g => .tensor .disj f.dual g.dual
  | _,_,.tensor .disj f g => .tensor .conj f.dual g.dual
  | _,_,.assocR .conj A B C => .assocL .disj A.dual B.dual C.dual
  | _,_,.assocR .disj A B C => .assocL .conj A.dual B.dual C.dual
  | _,_,.assocL .conj A B C => .assocR .disj A.dual B.dual C.dual
  | _,_,.assocL .disj A B C => .assocR .conj A.dual B.dual C.dual
  | _,_,.swap .conj A B => .swap .disj B.dual A.dual
  | _,_,.swap .disj A B => .swap .conj B.dual A.dual
  | _,_,.diag A => .codiag A.dual
  | _,_,.codiag A => .diag A.dual
  | _,_,.fst A B => .inl A.dual B.dual
  | _,_,.snd A B => .inr A.dual B.dual
  | _,_,.inl A B => .fst A.dual B.dual
  | _,_,.inr A B => .snd A.dual B.dual
  | _,_,.rightOut .conj A => .rightIn .disj A.dual
  | _,_,.rightOut .disj A => .rightIn .conj A.dual
  | _,_,.rightIn .conj A => .rightOut .disj A.dual
  | _,_,.rightIn .disj A => .rightOut .conj A.dual
  | _,_,.leftOut .conj A => .leftIn .disj A.dual
  | _,_,.leftOut .disj A => .leftIn .conj A.dual
  | _,_,.leftIn .conj A => .leftOut .disj A.dual
  | _,_,.leftIn .disj A => .leftOut .conj A.dual
  | _,_,.mix A B => .mix A.dual B.dual
  | _,_,.dist A B C => distRight A.dual B.dual C.dual
  | _,_,.zero A => .zero A.dual
  | _,_,.eta p => .epsilon p
  | _,_,.epsilon p => .eta p

end Term
end DosenPetric.Reduced
