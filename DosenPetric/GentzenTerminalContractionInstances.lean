module

public import DosenPetric.GentzenContractionFrameRanks
public import DosenPetric.GentzenTerminalContractionRouting

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.W1.DisjointContraction
universe u
variable {P : Type u} (d : TerminalContraction.Data P) (hn : 2 ≤ d.gs.length) (hm : 2 ≤ d.es.length)

section L
variable (Δ : List (NormalForm P)) (f : G P d.F Δ)

abbrev terminalInnerCL : G P d.FC Δ := W1.ContractionFrame.innerCL d.frame hn Δ f
abbrev terminalInnerEL : G P d.FE Δ := W1.ContractionFrame.innerEL d.frame hm Δ f
abbrev terminalOldL : G P d.K Δ := W1.ContractionFrame.oldL d.frame hn hm Δ f
abbrev terminalNewL : G P d.K Δ := W1.ContractionFrame.newL d.frame hn hm Δ f
abbrev terminalLCL := W1.ContractionFrame.LCL d.frame hn Δ f
abbrev terminalLEL := W1.ContractionFrame.LEL d.frame hm Δ f

theorem terminalDenoteL : ofTerm (terminalNewL d hn hm Δ f).denote = ofTerm (terminalOldL d hn hm Δ f).denote :=
  W1.ContractionFrame.denoteL d.frame d.square hn hm Δ f

theorem terminalOld_countL : (terminalOldL d hn hm Δ f).cutCount = f.cutCount := W1.ContractionFrame.oldL_count d.frame hn hm Δ f

theorem terminalOld_cutFreeL : (terminalOldL d hn hm Δ f).CutFree ↔ f.CutFree := W1.ContractionFrame.oldL_cutFree d.frame hn hm Δ f

theorem terminalOld_atomizedL : (terminalOldL d hn hm Δ f).Atomized ↔ f.Atomized := W1.ContractionFrame.oldL_atomized d.frame hn hm Δ f

theorem terminalNew_countL : (terminalNewL d hn hm Δ f).cutCount = f.cutCount := W1.ContractionFrame.newL_count d.frame hn hm Δ f

theorem terminalNew_cutFreeL : (terminalNewL d hn hm Δ f).CutFree ↔ f.CutFree := W1.ContractionFrame.newL_cutFree d.frame hn hm Δ f

theorem terminalNew_atomizedL : (terminalNewL d hn hm Δ f).Atomized ↔ f.Atomized := W1.ContractionFrame.newL_atomized d.frame hn hm Δ f

theorem terminalRelationL : (terminalNewL d hn hm Δ f).relation = (terminalOldL d hn hm Δ f).relation := congrArg occurrenceMap (terminalDenoteL ..)

theorem terminal_old_xCL : (terminalOldL d hn hm Δ f).rho .left d.xC = terminalLCL d hn Δ f+d.gs.length := W1.ContractionFrame.old_xCL d.frame d.square d.e1_keepC0 d.c1_keepE0 d.retained_distinct hn hm Δ f

theorem terminal_new_xCL : (terminalNewL d hn hm Δ f).rho .left d.xC = terminalLCL d hn Δ f+1 := W1.ContractionFrame.new_xCL d.frame d.e1_keepC0 d.retained_distinct hn hm Δ f

theorem terminal_old_xEL : (terminalOldL d hn hm Δ f).rho .left d.xE = terminalLEL d hm Δ f+1 := W1.ContractionFrame.old_xEL d.frame d.c1_keepE0 d.retained_distinct hn hm Δ f

theorem terminal_new_xEL : (terminalNewL d hn hm Δ f).rho .left d.xE = terminalLEL d hm Δ f+d.es.length := W1.ContractionFrame.new_xEL d.frame d.square d.e1_keepC0 d.c1_keepE0 d.retained_distinct hn hm Δ f

theorem terminalRankTableL :
    (terminalOldL d hn hm Δ f).rho .left d.xC = terminalLCL d hn Δ f+d.gs.length ∧
    (terminalNewL d hn hm Δ f).rho .left d.xC = terminalLCL d hn Δ f+1 ∧
    (terminalOldL d hn hm Δ f).rho .left d.xE = terminalLEL d hm Δ f+1 ∧
    (terminalNewL d hn hm Δ f).rho .left d.xE = terminalLEL d hm Δ f+d.es.length :=
  ⟨terminal_old_xCL ..,terminal_new_xCL ..,terminal_old_xEL ..,terminal_new_xEL ..⟩

abbrev terminal_oldC_contractionL := W1.ContractionFrame.oldC_contractionL d.frame d.square d.e1_keepC0 d.c1_keepE0 d.retained_distinct hn hm Δ f

abbrev terminal_newE_contractionL := W1.ContractionFrame.newE_contractionL d.frame d.square d.e1_keepC0 d.c1_keepE0 d.retained_distinct hn hm Δ f

abbrev terminal_C_balanceL := W1.ContractionFrame.C_balanceL d.frame d.square d.e1_keepC0 d.c1_keepE0 d.retained_distinct hn hm Δ f

abbrev terminal_E_balanceL := W1.ContractionFrame.E_balanceL d.frame d.square d.e1_keepC0 d.c1_keepE0 d.retained_distinct hn hm Δ f

abbrev terminal_C_decreasesL := W1.ContractionFrame.C_decreasesL d.frame d.square d.e1_keepC0 d.c1_keepE0 d.retained_distinct hn hm Δ f

abbrev terminal_E_increasesL := W1.ContractionFrame.E_increasesL d.frame d.square d.e1_keepC0 d.c1_keepE0 d.retained_distinct hn hm Δ f

abbrev terminal_C_subterm_ltL := W1.ContractionFrame.C_subterm_ltL d.frame d.square d.e1_keepC0 d.c1_keepE0 d.retained_distinct hn hm Δ f

abbrev terminal_E_subterm_ltL := W1.ContractionFrame.E_subterm_ltL d.frame d.square d.e1_keepC0 d.c1_keepE0 d.retained_distinct hn hm Δ f

abbrev terminal_sum_balanceL := W1.ContractionFrame.sum_balanceL d.frame d.square d.e1_keepC0 d.c1_keepE0 d.retained_distinct hn hm Δ f

abbrev terminalSumL (g : G P d.K Δ) := W1.ContractionFrame.endpointSumL d.frame Δ g

theorem terminal_sum_eqL (h : d.gs.length = d.es.length) : terminalSumL d Δ (terminalOldL d hn hm Δ f) = terminalSumL d Δ (terminalNewL d hn hm Δ f) :=
  W1.ContractionFrame.sum_eq_of_arity_eqL d.frame d.square d.e1_keepC0 d.c1_keepE0 d.retained_distinct hn hm Δ f h

theorem terminal_other_oldL {A : NormalForm P} (z : At d.K A) (hc : z.index ≠ d.xC.index) (he : z.index ≠ d.xE.index) :
    (terminalOldL d hn hm Δ f).rho .left z = 2+f.rho .left (d.frame.originalViaE d.c1_keepE0 z hc he) :=
  W1.ContractionFrame.other_oldL d.frame d.c1_keepE0 hn hm Δ f z hc he

theorem terminal_other_newL {A : NormalForm P} (z : At d.K A) (hc : z.index ≠ d.xC.index) (he : z.index ≠ d.xE.index) :
    (terminalNewL d hn hm Δ f).rho .left z = 2+f.rho .left (d.frame.originalViaE d.c1_keepE0 z hc he) :=
  W1.ContractionFrame.other_newL d.frame d.square d.e1_keepC0 d.c1_keepE0 hn hm Δ f z hc he

end L

theorem terminalTail_left (C E : NormalForm P) (gs hs : List (List (NormalForm P)))
    (H U V Δ : List (NormalForm P)) (hn : 2 ≤ gs.length) (hm : 2 ≤ (H::hs).length)
    (f : G P ((repeated C gs++U)++repeated E (H::hs)++V) Δ) :
    ofTerm (terminalNewL (TerminalContraction.terminalTail C E gs hs H U V) hn hm Δ f).denote =
    ofTerm (terminalOldL (TerminalContraction.terminalTail C E gs hs H U V) hn hm Δ f).denote := terminalDenoteL ..
section R
variable (Γ : List (NormalForm P)) (f : G P Γ d.F)

abbrev terminalInnerCR : G P Γ d.FC := W1.ContractionFrame.innerCR d.frame hn Γ f
abbrev terminalInnerER : G P Γ d.FE := W1.ContractionFrame.innerER d.frame hm Γ f
abbrev terminalOldR : G P Γ d.K := W1.ContractionFrame.oldR d.frame hn hm Γ f
abbrev terminalNewR : G P Γ d.K := W1.ContractionFrame.newR d.frame hn hm Γ f
abbrev terminalLCR := W1.ContractionFrame.LCR d.frame hn Γ f
abbrev terminalLER := W1.ContractionFrame.LER d.frame hm Γ f

theorem terminalDenoteR : ofTerm (terminalNewR d hn hm Γ f).denote = ofTerm (terminalOldR d hn hm Γ f).denote :=
  W1.ContractionFrame.denoteR d.frame d.square hn hm Γ f

theorem terminalOld_countR : (terminalOldR d hn hm Γ f).cutCount = f.cutCount := W1.ContractionFrame.oldR_count d.frame hn hm Γ f

theorem terminalOld_cutFreeR : (terminalOldR d hn hm Γ f).CutFree ↔ f.CutFree := W1.ContractionFrame.oldR_cutFree d.frame hn hm Γ f

theorem terminalOld_atomizedR : (terminalOldR d hn hm Γ f).Atomized ↔ f.Atomized := W1.ContractionFrame.oldR_atomized d.frame hn hm Γ f

theorem terminalNew_countR : (terminalNewR d hn hm Γ f).cutCount = f.cutCount := W1.ContractionFrame.newR_count d.frame hn hm Γ f

theorem terminalNew_cutFreeR : (terminalNewR d hn hm Γ f).CutFree ↔ f.CutFree := W1.ContractionFrame.newR_cutFree d.frame hn hm Γ f

theorem terminalNew_atomizedR : (terminalNewR d hn hm Γ f).Atomized ↔ f.Atomized := W1.ContractionFrame.newR_atomized d.frame hn hm Γ f

theorem terminalRelationR : (terminalNewR d hn hm Γ f).relation = (terminalOldR d hn hm Γ f).relation := congrArg occurrenceMap (terminalDenoteR ..)

theorem terminal_old_xCR : (terminalOldR d hn hm Γ f).rho .right d.xC = terminalLCR d hn Γ f+d.gs.length := W1.ContractionFrame.old_xCR d.frame d.square d.e1_keepC0 d.c1_keepE0 d.retained_distinct hn hm Γ f

theorem terminal_new_xCR : (terminalNewR d hn hm Γ f).rho .right d.xC = terminalLCR d hn Γ f+1 := W1.ContractionFrame.new_xCR d.frame d.e1_keepC0 d.retained_distinct hn hm Γ f

theorem terminal_old_xER : (terminalOldR d hn hm Γ f).rho .right d.xE = terminalLER d hm Γ f+1 := W1.ContractionFrame.old_xER d.frame d.c1_keepE0 d.retained_distinct hn hm Γ f

theorem terminal_new_xER : (terminalNewR d hn hm Γ f).rho .right d.xE = terminalLER d hm Γ f+d.es.length := W1.ContractionFrame.new_xER d.frame d.square d.e1_keepC0 d.c1_keepE0 d.retained_distinct hn hm Γ f

theorem terminalRankTableR :
    (terminalOldR d hn hm Γ f).rho .right d.xC = terminalLCR d hn Γ f+d.gs.length ∧
    (terminalNewR d hn hm Γ f).rho .right d.xC = terminalLCR d hn Γ f+1 ∧
    (terminalOldR d hn hm Γ f).rho .right d.xE = terminalLER d hm Γ f+1 ∧
    (terminalNewR d hn hm Γ f).rho .right d.xE = terminalLER d hm Γ f+d.es.length :=
  ⟨terminal_old_xCR ..,terminal_new_xCR ..,terminal_old_xER ..,terminal_new_xER ..⟩

abbrev terminal_oldC_contractionR := W1.ContractionFrame.oldC_contractionR d.frame d.square d.e1_keepC0 d.c1_keepE0 d.retained_distinct hn hm Γ f

abbrev terminal_newE_contractionR := W1.ContractionFrame.newE_contractionR d.frame d.square d.e1_keepC0 d.c1_keepE0 d.retained_distinct hn hm Γ f

abbrev terminal_C_balanceR := W1.ContractionFrame.C_balanceR d.frame d.square d.e1_keepC0 d.c1_keepE0 d.retained_distinct hn hm Γ f

abbrev terminal_E_balanceR := W1.ContractionFrame.E_balanceR d.frame d.square d.e1_keepC0 d.c1_keepE0 d.retained_distinct hn hm Γ f

abbrev terminal_C_decreasesR := W1.ContractionFrame.C_decreasesR d.frame d.square d.e1_keepC0 d.c1_keepE0 d.retained_distinct hn hm Γ f

abbrev terminal_E_increasesR := W1.ContractionFrame.E_increasesR d.frame d.square d.e1_keepC0 d.c1_keepE0 d.retained_distinct hn hm Γ f

abbrev terminal_C_subterm_ltR := W1.ContractionFrame.C_subterm_ltR d.frame d.square d.e1_keepC0 d.c1_keepE0 d.retained_distinct hn hm Γ f

abbrev terminal_E_subterm_ltR := W1.ContractionFrame.E_subterm_ltR d.frame d.square d.e1_keepC0 d.c1_keepE0 d.retained_distinct hn hm Γ f

abbrev terminal_sum_balanceR := W1.ContractionFrame.sum_balanceR d.frame d.square d.e1_keepC0 d.c1_keepE0 d.retained_distinct hn hm Γ f

abbrev terminalSumR (g : G P Γ d.K) := W1.ContractionFrame.endpointSumR d.frame Γ g

theorem terminal_sum_eqR (h : d.gs.length = d.es.length) : terminalSumR d Γ (terminalOldR d hn hm Γ f) = terminalSumR d Γ (terminalNewR d hn hm Γ f) :=
  W1.ContractionFrame.sum_eq_of_arity_eqR d.frame d.square d.e1_keepC0 d.c1_keepE0 d.retained_distinct hn hm Γ f h

theorem terminal_other_oldR {A : NormalForm P} (z : At d.K A) (hc : z.index ≠ d.xC.index) (he : z.index ≠ d.xE.index) :
    (terminalOldR d hn hm Γ f).rho .right z = 2+f.rho .right (d.frame.originalViaE d.c1_keepE0 z hc he) :=
  W1.ContractionFrame.other_oldR d.frame d.c1_keepE0 hn hm Γ f z hc he

theorem terminal_other_newR {A : NormalForm P} (z : At d.K A) (hc : z.index ≠ d.xC.index) (he : z.index ≠ d.xE.index) :
    (terminalNewR d hn hm Γ f).rho .right z = 2+f.rho .right (d.frame.originalViaE d.c1_keepE0 z hc he) :=
  W1.ContractionFrame.other_newR d.frame d.square d.e1_keepC0 d.c1_keepE0 hn hm Γ f z hc he

end R

theorem terminalTail_right (C E : NormalForm P) (gs hs : List (List (NormalForm P)))
    (H U V Γ : List (NormalForm P)) (hn : 2 ≤ gs.length) (hm : 2 ≤ (H::hs).length)
    (f : G P Γ ((repeated C gs++U)++repeated E (H::hs)++V)) :
    ofTerm (terminalNewR (TerminalContraction.terminalTail C E gs hs H U V) hn hm Γ f).denote =
    ofTerm (terminalOldR (TerminalContraction.terminalTail C E gs hs H U V) hn hm Γ f).denote := terminalDenoteR ..

end DosenPetric.Reduced.Gentzen.W1.DisjointContraction
