module

public import DosenPetric.GentzenStructuralProgramPositions

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace ContractionSelection
variable {F K : List (NormalForm P)} {C : NormalForm P}

def singleAt : {K : List (NormalForm P)}→{C : NormalForm P}→At K C→ContractionSelection C K K
  | _,_,.here C Θ=>.last Θ
  | _,_,@At.there _ C A Θ a=>.fixed A (singleAt a)

theorem singleAt_arity {A : NormalForm P} (a : At K A) : (singleAt a).arity=1 := by
  induction a with
  | here=>rfl
  | there a ih=>exact ih

theorem singleAt_keep {A : NormalForm P} (a : At K A) : (singleAt a).keep=a := by
  induction a with
  | here=>rfl
  | there a ih=>exact congrArg At.there ih

theorem singleAt_route {A : NormalForm P} (a : At K A) : (singleAt a).route=Route.identity K := by
  apply Route.ext_get
  intro B b
  rw [(singleAt a).singleton_get (singleAt_arity a),Route.get_identity]
  rfl

def program (p : ContractionSelection C F K) (hn : 2≤p.arity) : StructuralProgram P K F :=
  (StructuralProgram.contract C p.gs p.tail (p.blockArity hn)).reindex p.lower p.upper

theorem program_get (p : ContractionSelection C F K) (hn : 2≤p.arity)
    {A : NormalForm P} (a : At F A) : (p.program hn).get a=p.route.get a := by
  apply At.index_injective
  change (((copies C p.gs p.tail).get (a.cast p.upper.symm)).cast p.lower).index = _
  rw [At.index_cast,copies_index,At.index_cast,p.get_index]
end ContractionSelection

namespace StructuralProgram
variable {K U : List (NormalForm P)}

def empty : (K : List (NormalForm P))→StructuralProgram P K []
  | []=>.identity []
  | A::K=>.seq (.thin [] K A) (empty K)

def duplicateHead {A : NormalForm P} (a : At K A) : StructuralProgram P K (A::K) :=
  (ContractionSelection.more (ContractionSelection.singleAt a)).program
    (by change (ContractionSelection.singleAt a).arity+1≥2;rw [ContractionSelection.singleAt_arity];omega)

theorem duplicateHead_here {A : NormalForm P} (a : At K A) :
    (duplicateHead a).get (.here A K)=a := by
  rw [duplicateHead,ContractionSelection.program_get]
  exact ContractionSelection.singleAt_keep a

theorem duplicateHead_there {A B : NormalForm P} (a : At K A) (b : At K B) :
    (duplicateHead a).get b.there=b := by
  rw [duplicateHead,ContractionSelection.program_get]
  change (ContractionSelection.singleAt a).route.get b=b
  rw [ContractionSelection.singleAt_route,Route.get_identity]
end StructuralProgram

namespace Route
variable {K U : List (NormalForm P)}

/-- Realization by existing exchange, thinning and separated contraction
rules. No equality of interpreted relations is used. -/
def program : {U : List (NormalForm P)}→Route K U→StructuralProgram P K U
  | _,.nil=>.empty K
  | _,.cons a r=>.seq (.duplicateHead a) (r.program.consFixed _)

theorem program_get (r : Route K U) {A : NormalForm P} (a : At U A) :
    r.program.get a=r.get a := by
  induction r with
  | nil=>cases a
  | @cons A U b r ih=>
    cases a with
    | here=>
      change (StructuralProgram.duplicateHead b).get ((r.program.consFixed A).get (.here A _))=b
      rw [StructuralProgram.consFixed_here,StructuralProgram.duplicateHead_here]
    | there a=>
      change (StructuralProgram.duplicateHead b).get ((r.program.consFixed A).get a.there)=r.get a
      rw [StructuralProgram.consFixed_there,StructuralProgram.duplicateHead_there,ih]

theorem program_arrow (r : Route K U) (o : Op) : r.program.arrow o=r.sideArrow o := by
  apply side_ext o
  intro A a
  rw [StructuralProgram.component,Route.sideArrow_get,program_get]
end Route
end DosenPetric.Reduced.Gentzen
