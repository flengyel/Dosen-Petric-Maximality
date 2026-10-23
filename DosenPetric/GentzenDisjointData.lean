module

public import DosenPetric.GentzenDisjointIndices

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.Disjoint
universe u
variable {P : Type u}

/-- Original fixed-gap data only; no square or rank conclusion is a field. -/
structure Data (P : Type u) where
  C : NormalForm P
  E : NormalForm P
  pre : List (List (NormalForm P))
  post : List (List (NormalForm P))
  hs : List (List (NormalForm P))
  H : List (NormalForm P)
  U : List (NormalForm P)
  V : List (NormalForm P)
  Θ : List (NormalForm P)

def fixedGap (C E : NormalForm P) (pre post hs : List (List (NormalForm P)))
    (H U V Θ : List (NormalForm P)) : Data P := ⟨C,E,pre,post,hs,H,U,V,Θ⟩

namespace Data
variable (d : Data P)
abbrev es := d.H :: d.hs
abbrev outer0 := d.pre ++ (d.U ++ (repeated d.E d.es ++ d.V)) :: d.post
abbrev outer1 := d.pre ++ (d.U ++ (gaps d.es ++ d.E :: d.V)) :: d.post
abbrev upBefore := repeated d.C d.pre ++ d.U
abbrev upAfter := d.V ++ d.C :: (repeated d.C d.post ++ d.Θ)
abbrev loBefore := gaps d.pre ++ d.U
abbrev loAfter := d.V ++ (gaps d.post ++ d.C :: d.Θ)
abbrev eUpper := (d.upBefore ++ d.H) :: d.hs
abbrev eLower := (d.loBefore ++ d.H) :: d.hs
abbrev F := d.upBefore ++ repeated d.E d.es ++ d.upAfter
abbrev FE := d.upBefore ++ gaps d.es ++ d.E :: d.upAfter
abbrev FC := d.loBefore ++ repeated d.E d.es ++ d.loAfter
abbrev K := d.loBefore ++ gaps d.es ++ d.E :: d.loAfter

theorem upperC0 : repeated d.C d.outer0 ++ d.Θ = d.F := by
  simp only [outer0,F,upBefore,upAfter,GapInsertion.repeated_append,repeated,List.append_assoc,List.cons_append]
theorem lowerC0 : gaps d.outer0 ++ d.C :: d.Θ = d.FC := by
  simp only [outer0,FC,loBefore,loAfter,GapInsertion.gaps_append,gaps,List.append_assoc]
theorem upperC1 : repeated d.C d.outer1 ++ d.Θ = d.FE := by
  simp only [outer1,FE,upBefore,upAfter,GapInsertion.repeated_append,repeated,List.append_assoc,List.cons_append]
theorem lowerC1 : gaps d.outer1 ++ d.C :: d.Θ = d.K := by
  simp only [outer1,K,loBefore,loAfter,GapInsertion.gaps_append,gaps,List.append_assoc,List.cons_append]
theorem upperE0 : repeated d.E d.eUpper ++ d.upAfter = d.F := by
  simp only [F,repeated,List.append_assoc,List.cons_append]
theorem lowerE0 : gaps d.eUpper ++ d.E :: d.upAfter = d.FE := by
  simp only [FE,gaps,List.append_assoc]
theorem upperE1 : repeated d.E d.eLower ++ d.loAfter = d.FC := by
  simp only [FC,repeated,List.append_assoc,List.cons_append]
theorem lowerE1 : gaps d.eLower ++ d.E :: d.loAfter = d.K := by
  simp only [K,gaps,List.append_assoc]
theorem countC : d.outer1.length = d.outer0.length := by simp only [outer0,outer1,List.length_append,List.length_cons]
theorem countE0 : d.eUpper.length = d.es.length := rfl
theorem countE1 : d.eLower.length = d.es.length := rfl

abbrev bc0 : ContractionBlock P d.F d.FC := ⟨d.C,d.outer0,d.Θ,d.upperC0,d.lowerC0⟩
abbrev bc1 : ContractionBlock P d.FE d.K := ⟨d.C,d.outer1,d.Θ,d.upperC1,d.lowerC1⟩
abbrev be0 : ContractionBlock P d.F d.FE := ⟨d.E,d.eUpper,d.upAfter,d.upperE0,d.lowerE0⟩
abbrev be1 : ContractionBlock P d.FC d.K := ⟨d.E,d.eLower,d.loAfter,d.upperE1,d.lowerE1⟩
abbrev c0 := d.bc0.route
abbrev c1 := d.bc1.route
abbrev e0 := d.be0.route
abbrev e1 := d.be1.route
abbrev selectedC0 := d.bc0.selected
abbrev selectedC1 := d.bc1.selected
abbrev selectedE0 := d.be0.selected
abbrev selectedE1 := d.be1.selected
abbrev keepC0 := d.bc0.keep
abbrev keepE0 := d.be0.keep
abbrev xC := d.bc1.keep
abbrev xE := d.be1.keep

theorem xE_index : d.xE.index = d.loBefore.length+(gaps d.es).length := by
  rw [ContractionBlock.keep_index]
  simp only [gaps,List.length_append]
  omega

theorem xC_index : d.xC.index = d.xE.index+1+d.V.length+(gaps d.post).length := by
  rw [ContractionBlock.keep_index,d.xE_index]
  simp only [outer1,GapInsertion.gaps_append,gaps,List.length_append,List.length_cons,loBefore]
  omega

theorem retained_order : d.xE.index < d.xC.index := by have h := d.xC_index; omega

theorem keepE0_index : d.keepE0.index = d.upBefore.length+(gaps d.es).length := by
  rw [ContractionBlock.keep_index]
  simp only [gaps,List.length_append]
  omega

theorem keepC0_index : d.keepC0.index = d.loBefore.length+(repeated d.E d.es).length+d.V.length+(gaps d.post).length := by
  rw [ContractionBlock.keep_index]
  simp only [outer0,GapInsertion.gaps_append,gaps,List.length_append,loBefore]
  omega

theorem e0_index {A : NormalForm P} (a : At d.F A) :
    (d.e0.get a).index = splice d.upBefore.length (repeated d.E d.es).length
      ((gaps d.es).length+1) (copyIndex d.es) a.index := by
  rw [ContractionBlock.get_index]
  exact copy_splice d.E d.upBefore d.H d.hs a.index

theorem e1_index {A : NormalForm P} (a : At d.FC A) :
    (d.e1.get a).index = splice d.loBefore.length (repeated d.E d.es).length
      ((gaps d.es).length+1) (copyIndex d.es) a.index := by
  rw [ContractionBlock.get_index]
  exact copy_splice d.E d.loBefore d.H d.hs a.index

theorem square {A : NormalForm P} (a : At d.F A) : d.c1.get (d.e0.get a) = d.e1.get (d.c0.get a) := by
  apply At.index_injective
  rw [ContractionBlock.get_index,d.e0_index,d.e1_index,ContractionBlock.get_index]
  have h := copy_splice_square d.C d.pre d.post d.U (repeated d.E d.es) (gaps d.es ++ [d.E]) d.V
    (copyIndex d.es) (fun j hj => by simpa only [List.length_append,List.length_singleton] using copy_bound d.E d.es j hj) a.index
  simpa only [bc0,bc1,outer0,outer1,upBefore,loBefore,List.append_assoc,List.singleton_append,List.length_append,List.length_singleton,Nat.add_assoc] using h

theorem product_square : comp (ofTerm d.c1.product) (ofTerm d.e0.product) = comp (ofTerm d.e1.product) (ofTerm d.c0.product) := by
  apply product_positions
  intro A a
  rw [Laws.assoc,Route.product_get,Route.product_get,Laws.assoc,Route.product_get,Route.product_get]
  exact congrArg (fun x => ofTerm x.projection) (d.square a)

theorem coproduct_square : comp (ofTerm d.e0.coproduct) (ofTerm d.c1.coproduct) = comp (ofTerm d.c0.coproduct) (ofTerm d.e1.coproduct) := by
  apply coproduct_positions
  intro A a
  rw [← Laws.assoc,Route.coproduct_get,Route.coproduct_get,← Laws.assoc,Route.coproduct_get,Route.coproduct_get]
  exact congrArg (fun x => ofTerm x.injection) (d.square a)

end Data
end DosenPetric.Reduced.Gentzen.Disjoint
