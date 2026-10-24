module

public import DosenPetric.GentzenContractionFrameFibers

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.TerminalContraction
universe u
variable {P : Type u}

/-- Original terminal-tail inputs, with no desired law as a field. -/
structure Data (P : Type u) where
  C : NormalForm P
  E : NormalForm P
  gs : List (List (NormalForm P))
  hs : List (List (NormalForm P))
  H : List (NormalForm P)
  U : List (NormalForm P)
  V : List (NormalForm P)

def terminalTail (C E : NormalForm P) (gs hs : List (List (NormalForm P)))
    (H U V : List (NormalForm P)) : Data P := ⟨C,E,gs,hs,H,U,V⟩

namespace Data
variable (d : Data P)
abbrev es := d.H :: d.hs
abbrev upBefore := repeated d.C d.gs ++ d.U
abbrev loBefore := gaps d.gs ++ d.C :: d.U
abbrev F := d.upBefore ++ repeated d.E d.es ++ d.V
abbrev FE := d.upBefore ++ gaps d.es ++ d.E :: d.V
abbrev FC := d.loBefore ++ repeated d.E d.es ++ d.V
abbrev K := d.loBefore ++ gaps d.es ++ d.E :: d.V
abbrev tailC0 := d.U ++ repeated d.E d.es ++ d.V
abbrev tailC1 := d.U ++ gaps d.es ++ d.E :: d.V
abbrev eUpper := (d.upBefore ++ d.H) :: d.hs
abbrev eLower := (d.loBefore ++ d.H) :: d.hs

theorem upperC0 : repeated d.C d.gs ++ d.tailC0 = d.F := by
  simp only [tailC0,F,upBefore,List.append_assoc]
theorem lowerC0 : gaps d.gs ++ d.C :: d.tailC0 = d.FC := by
  simp only [tailC0,FC,loBefore,List.append_assoc,List.cons_append]
theorem upperC1 : repeated d.C d.gs ++ d.tailC1 = d.FE := by
  simp only [tailC1,FE,upBefore,List.append_assoc]
theorem lowerC1 : gaps d.gs ++ d.C :: d.tailC1 = d.K := by
  simp only [tailC1,K,loBefore,List.append_assoc,List.cons_append]
theorem upperE0 : repeated d.E d.eUpper ++ d.V = d.F := by
  simp only [F,repeated,List.append_assoc,List.cons_append]
theorem lowerE0 : gaps d.eUpper ++ d.E :: d.V = d.FE := by
  simp only [FE,gaps,List.append_assoc]
theorem upperE1 : repeated d.E d.eLower ++ d.V = d.FC := by
  simp only [FC,repeated,List.append_assoc,List.cons_append]
theorem lowerE1 : gaps d.eLower ++ d.E :: d.V = d.K := by
  simp only [K,gaps,List.append_assoc]
theorem countE0 : d.eUpper.length = d.es.length := rfl
theorem countE1 : d.eLower.length = d.es.length := rfl

/-- All eight identifications are proved above, rather than assumed routing data. -/
abbrev frame : ContractionFrame P where
  C := d.C; E := d.E
  cgs0 := d.gs; cgs1 := d.gs; egs0 := d.eUpper; egs1 := d.eLower
  ct0 := d.tailC0; ct1 := d.tailC1; et0 := d.V; et1 := d.V
  F := d.F; FE := d.FE; FC := d.FC; K := d.K
  upperC0 := d.upperC0; lowerC0 := d.lowerC0; upperC1 := d.upperC1; lowerC1 := d.lowerC1
  upperE0 := d.upperE0; lowerE0 := d.lowerE0; upperE1 := d.upperE1; lowerE1 := d.lowerE1
  countC := rfl; countE := rfl

abbrev c0 := d.frame.c0
abbrev c1 := d.frame.c1
abbrev e0 := d.frame.e0
abbrev e1 := d.frame.e1
abbrev selectedC0 := d.frame.selectedC0
abbrev selectedC1 := d.frame.selectedC1
abbrev selectedE0 := d.frame.selectedE0
abbrev selectedE1 := d.frame.selectedE1
abbrev xC := d.frame.xC
abbrev xE := d.frame.xE
abbrev keepC0 := d.frame.keepC0
abbrev keepE0 := d.frame.keepE0

theorem xC_index : d.xC.index = (gaps d.gs).length := d.frame.bc1.keep_index

theorem xE_index : d.xE.index = (gaps d.gs).length+1+d.U.length+(gaps d.es).length := by
  rw [ContractionBlock.keep_index]
  simp only [gaps,List.length_append,List.length_cons]
  omega

theorem retained_order : d.xC.index < d.xE.index := by
  rw [d.xC_index,d.xE_index]
  omega

theorem retained_distinct : d.frame.xC.index ≠ d.frame.xE.index := by
  have h := d.retained_order
  change d.xC.index ≠ d.xE.index
  omega

theorem keepC0_index : d.keepC0.index = (gaps d.gs).length := d.frame.bc0.keep_index

theorem keepE0_index : d.keepE0.index = d.upBefore.length+(gaps d.es).length := by
  rw [ContractionBlock.keep_index]
  simp only [gaps,List.length_append]
  omega

end Data
end DosenPetric.Reduced.Gentzen.TerminalContraction
