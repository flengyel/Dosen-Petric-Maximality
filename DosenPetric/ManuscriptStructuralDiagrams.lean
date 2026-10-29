module

public import DosenPetric.CartesianClosureObstruction

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Presentation.ManuscriptDiagrams
universe u
variable {P : Type u}

def firstUpper (A B C : Formula P) : Hom (.conj A B) (.conj A (.disj B C)) :=
  tensor .conj (id A) (inl B C)
def firstRight (A B C : Formula P) : Hom (.conj A (.disj B C)) (.disj (.conj A B) C) := dist A B C
def firstDiagonal (A B C : Formula P) : Hom (.conj A B) (.disj (.conj A B) C) := inl (.conj A B) C

/-- Appendix B's first triangle, with its actual source arrow paths. -/
theorem first_triangle (A B C : Formula P) :
    comp (firstUpper A B C) (firstRight A B C) = firstDiagonal A B C := (Laws.dist_inl A B C).symm

def zeroStart (A : Formula P) : Hom A (.conj A .top) := pair (id A) (toTop A)
def zeroEta (A : Formula P) : Hom (.conj A .top) (.conj A (.disj (.neg A) A)) :=
  tensor .conj (id A) (excludedMiddle A)
def zeroDistributor (A : Formula P) : Hom (.conj A (.disj (.neg A) A)) (.disj (.conj A (.neg A)) A) :=
  dist A (.neg A) A
def zeroEpsilon (A : Formula P) : Hom (.disj (.conj A (.neg A)) A) (.disj .bot A) :=
  tensor .disj (contradiction A) (id A)
def zeroEnd (A : Formula P) : Hom (.disj .bot A) A := copair (fromBot A) (id A)

def zeroPath (A : Formula P) : Hom A A :=
  comp (zeroStart A) (comp (zeroEta A) (comp (zeroDistributor A) (comp (zeroEpsilon A) (zeroEnd A))))

/-- Appendix B's five-arrow path is exactly the source-defined zero identity. -/
theorem zero_diagram (A : Formula P) : zeroPath A = (zeroIdentity P).zero A :=
  (zeroConstruction_structural A).symm

theorem zero_primitive (A : Formula P) : zeroPath A = zero A :=
  (zero_diagram A).trans (zeroConstruction_eq A)

/-- Appendix B's two square paths, for arbitrary existing parallel f and g. -/
theorem zero_square {A B : Formula P} (f g : Hom A B) :
    comp (zeroPath A) f = comp g (zeroPath B) := by
  rw [zero_diagram,zero_diagram]
  exact (zeroIdentity P).law f g

end DosenPetric.Presentation.ManuscriptDiagrams
