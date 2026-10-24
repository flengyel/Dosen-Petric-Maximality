module

public import DosenPetric.GentzenContractionFrameCommutation

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

namespace W1.ContractionFrame
variable (d : ContractionFrame P)
variable (hSq : ∀ {A : NormalForm P} (a : At d.F A), d.c1.get (d.e0.get a) = d.e1.get (d.c0.get a))
variable (hC : d.e1.get d.keepC0 = d.xC) (hE : d.c1.get d.keepE0 = d.xE)
variable (hSep : d.xC.index ≠ d.xE.index)
variable (hn : 2 ≤ d.cgs0.length) (hm : 2 ≤ d.egs0.length)

section L
variable (Δ : List (NormalForm P)) (f : G P d.F Δ)

def LCL := d.bc0.rankL hn Δ f
def LEL := d.be0.rankL hm Δ f

include hSq hC hE hSep in
theorem oldC_contractionL : d.bc1.rankL (outerArity d hn) Δ (innerEL d hm Δ f) = LCL d hn Δ f+d.cgs0.length := by
  have h₀ := d.bc0.rankL_sum hn Δ f
  have h₁ := d.bc1.rankL_sum (outerArity d hn) Δ (innerEL d hm Δ f)
  have hs : (d.selectedC1.map (fun a => (innerEL d hm Δ f).rho .left a)).sum =
      (d.selectedC0.map (fun a => f.rho .left a)).sum+d.selectedC0.length := by
    apply sum_transport_one _ _ d.e0.get _ _ (d.selectedC_transport hSq hC hE hSep)
    intro a ha
    exact d.be0.rankL_fixed hm Δ f (d.e0.get a) a (d.selectedC0_parametric hSq hC hE hSep a ha) rfl
  have hl := d.selectedC0_length
  change LCL d hn Δ f = 1+(d.selectedC0.map (fun a => f.rho .left a)).sum at h₀
  change d.bc1.rankL (outerArity d hn) Δ (innerEL d hm Δ f) =
    1+(d.selectedC1.map (fun a => (innerEL d hm Δ f).rho .left a)).sum at h₁
  omega

include hSq hC hE hSep in
theorem newE_contractionL : d.be1.rankL (innerArity d hm) Δ (innerCL d hn Δ f) = LEL d hm Δ f+d.egs0.length := by
  have h₀ := d.be0.rankL_sum hm Δ f
  have h₁ := d.be1.rankL_sum (innerArity d hm) Δ (innerCL d hn Δ f)
  have hs : (d.selectedE1.map (fun a => (innerCL d hn Δ f).rho .left a)).sum =
      (d.selectedE0.map (fun a => f.rho .left a)).sum+d.selectedE0.length := by
    apply sum_transport_one _ _ d.c0.get _ _ (d.selectedE_transport hSq hC hE hSep)
    intro a ha
    exact d.bc0.rankL_fixed hn Δ f (d.c0.get a) a (d.selectedE0_parametric hSq hC hE hSep a ha) rfl
  have hl := d.selectedE0_length
  change LEL d hm Δ f = 1+(d.selectedE0.map (fun a => f.rho .left a)).sum at h₀
  change d.be1.rankL (innerArity d hm) Δ (innerCL d hn Δ f) =
    1+(d.selectedE1.map (fun a => (innerCL d hn Δ f).rho .left a)).sum at h₁
  omega

include hSq hC hE hSep in
theorem old_xCL : (oldL d hn hm Δ f).rho .left d.xC = LCL d hn Δ f+d.cgs0.length :=
  (d.bc1.rankL_keep (outerArity d hn) Δ _).trans (oldC_contractionL d hSq hC hE hSep hn hm Δ f)

include hSq hC hE hSep in
theorem new_xEL : (newL d hn hm Δ f).rho .left d.xE = LEL d hm Δ f+d.egs0.length :=
  (d.be1.rankL_keep (innerArity d hm) Δ _).trans (newE_contractionL d hSq hC hE hSep hn hm Δ f)

include hC hSep in
theorem new_xCL : (newL d hn hm Δ f).rho .left d.xC = LCL d hn Δ f+1 := by
  have h := d.be1.rankL_fixed (innerArity d hm) Δ (innerCL d hn Δ f) d.xC d.keepC0
    (by change d.xC.index ≠ d.xE.index; exact hSep) hC
  have h' := d.bc0.rankL_keep hn Δ f
  change (newL d hn hm Δ f).rho .left d.xC = 1+(innerCL d hn Δ f).rho .left d.keepC0 at h
  exact h.trans ((congrArg (fun n : Nat => 1+n) h').trans (Nat.add_comm ..))

include hE hSep in
theorem old_xEL : (oldL d hn hm Δ f).rho .left d.xE = LEL d hm Δ f+1 := by
  have h := d.bc1.rankL_fixed (outerArity d hn) Δ (innerEL d hm Δ f) d.xE d.keepE0
    (by change d.xE.index ≠ d.xC.index; exact hSep.symm) hE
  have h' := d.be0.rankL_keep hm Δ f
  change (oldL d hn hm Δ f).rho .left d.xE = 1+(innerEL d hm Δ f).rho .left d.keepE0 at h
  exact h.trans ((congrArg (fun n : Nat => 1+n) h').trans (Nat.add_comm ..))

include hSq hC hE hSep in
theorem C_balanceL : (oldL d hn hm Δ f).rho .left d.xC+1 = (newL d hn hm Δ f).rho .left d.xC+d.cgs0.length := by
  have h0 := old_xCL d hSq hC hE hSep hn hm Δ f
  have h1 := new_xCL d hC hSep hn hm Δ f
  omega

include hSq hC hE hSep in
theorem E_balanceL : (newL d hn hm Δ f).rho .left d.xE+1 = (oldL d hn hm Δ f).rho .left d.xE+d.egs0.length := by
  have h0 := old_xEL d hE hSep hn hm Δ f
  have h1 := new_xEL d hSq hC hE hSep hn hm Δ f
  omega

include hSq hC hE hSep in
theorem C_decreasesL : (newL d hn hm Δ f).rho .left d.xC < (oldL d hn hm Δ f).rho .left d.xC := by
  have h0 := old_xCL d hSq hC hE hSep hn hm Δ f
  have h1 := new_xCL d hC hSep hn hm Δ f
  omega

include hSq hC hE hSep in
theorem E_increasesL : (oldL d hn hm Δ f).rho .left d.xE < (newL d hn hm Δ f).rho .left d.xE := by
  have h0 := old_xEL d hE hSep hn hm Δ f
  have h1 := new_xEL d hSq hC hE hSep hn hm Δ f
  omega

include hSq hC hE hSep in
theorem C_subterm_ltL : LCL d hn Δ f < (oldL d hn hm Δ f).rho .left d.xC := by
  have h0 := old_xCL d hSq hC hE hSep hn hm Δ f
  omega

include hSq hC hE hSep in
theorem E_subterm_ltL : LEL d hm Δ f < (newL d hn hm Δ f).rho .left d.xE := by
  have h0 := new_xEL d hSq hC hE hSep hn hm Δ f
  omega

def endpointSumL (g : G P d.K Δ) : Nat := g.rho .left d.xC+g.rho .left d.xE

include hSq hC hE hSep in
theorem sum_balanceL : endpointSumL d Δ (oldL d hn hm Δ f)+d.egs0.length =
    endpointSumL d Δ (newL d hn hm Δ f)+d.cgs0.length := by
  change (oldL d hn hm Δ f).rho .left d.xC+(oldL d hn hm Δ f).rho .left d.xE+d.egs0.length =
    (newL d hn hm Δ f).rho .left d.xC+(newL d hn hm Δ f).rho .left d.xE+d.cgs0.length
  have h₀ := old_xCL d hSq hC hE hSep hn hm Δ f
  have h₁ := old_xEL d hE hSep hn hm Δ f
  have h₂ := new_xCL d hC hSep hn hm Δ f
  have h₃ := new_xEL d hSq hC hE hSep hn hm Δ f
  omega

include hSq hC hE hSep in
theorem sum_eq_of_arity_eqL (h : d.cgs0.length = d.egs0.length) :
    endpointSumL d Δ (oldL d hn hm Δ f) = endpointSumL d Δ (newL d hn hm Δ f) := by
  have h' := sum_balanceL d hSq hC hE hSep hn hm Δ f
  omega

theorem other_oldL {A : NormalForm P} (z : At d.K A)
    (hc : z.index ≠ d.xC.index) (he : z.index ≠ d.xE.index) :
    (oldL d hn hm Δ f).rho .left z = 2+f.rho .left (d.originalViaE hE z hc he) := by
  have h := d.bc1.rankL_fixed (outerArity d hn) Δ (innerEL d hm Δ f) z (d.middleE z hc) hc (d.middleE_get z hc)
  have h' := d.be0.rankL_fixed hm Δ f (d.middleE z hc) (d.originalViaE hE z hc he)
    (d.middleE_fixed hE z hc he) (d.originalViaE_get hE z hc he)
  exact h.trans ((congrArg (fun n : Nat => 1+n) h').trans (by omega))

include hSq hC in
theorem other_newL {A : NormalForm P} (z : At d.K A)
    (hc : z.index ≠ d.xC.index) (he : z.index ≠ d.xE.index) :
    (newL d hn hm Δ f).rho .left z = 2+f.rho .left (d.originalViaE hE z hc he) := by
  have h := d.be1.rankL_fixed (innerArity d hm) Δ (innerCL d hn Δ f) z (d.middleC z he) he (d.middleC_get z he)
  have h' := d.bc0.rankL_fixed hn Δ f (d.middleC z he) (d.originalViaE hE z hc he)
    (d.middleC_fixed hC z hc he) (d.other_c0_get hSq hC hE z hc he)
  exact h.trans ((congrArg (fun n : Nat => 1+n) h').trans (by omega))

end L

section R
variable (Γ : List (NormalForm P)) (f : G P Γ d.F)

def LCR := d.bc0.rankR hn Γ f
def LER := d.be0.rankR hm Γ f

include hSq hC hE hSep in
theorem oldC_contractionR : d.bc1.rankR (outerArity d hn) Γ (innerER d hm Γ f) = LCR d hn Γ f+d.cgs0.length := by
  have h₀ := d.bc0.rankR_sum hn Γ f
  have h₁ := d.bc1.rankR_sum (outerArity d hn) Γ (innerER d hm Γ f)
  have hs : (d.selectedC1.map (fun a => (innerER d hm Γ f).rho .right a)).sum =
      (d.selectedC0.map (fun a => f.rho .right a)).sum+d.selectedC0.length := by
    apply sum_transport_one _ _ d.e0.get _ _ (d.selectedC_transport hSq hC hE hSep)
    intro a ha
    exact d.be0.rankR_fixed hm Γ f (d.e0.get a) a (d.selectedC0_parametric hSq hC hE hSep a ha) rfl
  have hl := d.selectedC0_length
  change LCR d hn Γ f = 1+(d.selectedC0.map (fun a => f.rho .right a)).sum at h₀
  change d.bc1.rankR (outerArity d hn) Γ (innerER d hm Γ f) =
    1+(d.selectedC1.map (fun a => (innerER d hm Γ f).rho .right a)).sum at h₁
  omega

include hSq hC hE hSep in
theorem newE_contractionR : d.be1.rankR (innerArity d hm) Γ (innerCR d hn Γ f) = LER d hm Γ f+d.egs0.length := by
  have h₀ := d.be0.rankR_sum hm Γ f
  have h₁ := d.be1.rankR_sum (innerArity d hm) Γ (innerCR d hn Γ f)
  have hs : (d.selectedE1.map (fun a => (innerCR d hn Γ f).rho .right a)).sum =
      (d.selectedE0.map (fun a => f.rho .right a)).sum+d.selectedE0.length := by
    apply sum_transport_one _ _ d.c0.get _ _ (d.selectedE_transport hSq hC hE hSep)
    intro a ha
    exact d.bc0.rankR_fixed hn Γ f (d.c0.get a) a (d.selectedE0_parametric hSq hC hE hSep a ha) rfl
  have hl := d.selectedE0_length
  change LER d hm Γ f = 1+(d.selectedE0.map (fun a => f.rho .right a)).sum at h₀
  change d.be1.rankR (innerArity d hm) Γ (innerCR d hn Γ f) =
    1+(d.selectedE1.map (fun a => (innerCR d hn Γ f).rho .right a)).sum at h₁
  omega

include hSq hC hE hSep in
theorem old_xCR : (oldR d hn hm Γ f).rho .right d.xC = LCR d hn Γ f+d.cgs0.length :=
  (d.bc1.rankR_keep (outerArity d hn) Γ _).trans (oldC_contractionR d hSq hC hE hSep hn hm Γ f)

include hSq hC hE hSep in
theorem new_xER : (newR d hn hm Γ f).rho .right d.xE = LER d hm Γ f+d.egs0.length :=
  (d.be1.rankR_keep (innerArity d hm) Γ _).trans (newE_contractionR d hSq hC hE hSep hn hm Γ f)

include hC hSep in
theorem new_xCR : (newR d hn hm Γ f).rho .right d.xC = LCR d hn Γ f+1 := by
  have h := d.be1.rankR_fixed (innerArity d hm) Γ (innerCR d hn Γ f) d.xC d.keepC0
    (by change d.xC.index ≠ d.xE.index; exact hSep) hC
  have h' := d.bc0.rankR_keep hn Γ f
  change (newR d hn hm Γ f).rho .right d.xC = 1+(innerCR d hn Γ f).rho .right d.keepC0 at h
  exact h.trans ((congrArg (fun n : Nat => 1+n) h').trans (Nat.add_comm ..))

include hE hSep in
theorem old_xER : (oldR d hn hm Γ f).rho .right d.xE = LER d hm Γ f+1 := by
  have h := d.bc1.rankR_fixed (outerArity d hn) Γ (innerER d hm Γ f) d.xE d.keepE0
    (by change d.xE.index ≠ d.xC.index; exact hSep.symm) hE
  have h' := d.be0.rankR_keep hm Γ f
  change (oldR d hn hm Γ f).rho .right d.xE = 1+(innerER d hm Γ f).rho .right d.keepE0 at h
  exact h.trans ((congrArg (fun n : Nat => 1+n) h').trans (Nat.add_comm ..))

include hSq hC hE hSep in
theorem C_balanceR : (oldR d hn hm Γ f).rho .right d.xC+1 = (newR d hn hm Γ f).rho .right d.xC+d.cgs0.length := by
  have h0 := old_xCR d hSq hC hE hSep hn hm Γ f
  have h1 := new_xCR d hC hSep hn hm Γ f
  omega

include hSq hC hE hSep in
theorem E_balanceR : (newR d hn hm Γ f).rho .right d.xE+1 = (oldR d hn hm Γ f).rho .right d.xE+d.egs0.length := by
  have h0 := old_xER d hE hSep hn hm Γ f
  have h1 := new_xER d hSq hC hE hSep hn hm Γ f
  omega

include hSq hC hE hSep in
theorem C_decreasesR : (newR d hn hm Γ f).rho .right d.xC < (oldR d hn hm Γ f).rho .right d.xC := by
  have h0 := old_xCR d hSq hC hE hSep hn hm Γ f
  have h1 := new_xCR d hC hSep hn hm Γ f
  omega

include hSq hC hE hSep in
theorem E_increasesR : (oldR d hn hm Γ f).rho .right d.xE < (newR d hn hm Γ f).rho .right d.xE := by
  have h0 := old_xER d hE hSep hn hm Γ f
  have h1 := new_xER d hSq hC hE hSep hn hm Γ f
  omega

include hSq hC hE hSep in
theorem C_subterm_ltR : LCR d hn Γ f < (oldR d hn hm Γ f).rho .right d.xC := by
  have h0 := old_xCR d hSq hC hE hSep hn hm Γ f
  omega

include hSq hC hE hSep in
theorem E_subterm_ltR : LER d hm Γ f < (newR d hn hm Γ f).rho .right d.xE := by
  have h0 := new_xER d hSq hC hE hSep hn hm Γ f
  omega

def endpointSumR (g : G P Γ d.K) : Nat := g.rho .right d.xC+g.rho .right d.xE

include hSq hC hE hSep in
theorem sum_balanceR : endpointSumR d Γ (oldR d hn hm Γ f)+d.egs0.length =
    endpointSumR d Γ (newR d hn hm Γ f)+d.cgs0.length := by
  change (oldR d hn hm Γ f).rho .right d.xC+(oldR d hn hm Γ f).rho .right d.xE+d.egs0.length =
    (newR d hn hm Γ f).rho .right d.xC+(newR d hn hm Γ f).rho .right d.xE+d.cgs0.length
  have h₀ := old_xCR d hSq hC hE hSep hn hm Γ f
  have h₁ := old_xER d hE hSep hn hm Γ f
  have h₂ := new_xCR d hC hSep hn hm Γ f
  have h₃ := new_xER d hSq hC hE hSep hn hm Γ f
  omega

include hSq hC hE hSep in
theorem sum_eq_of_arity_eqR (h : d.cgs0.length = d.egs0.length) :
    endpointSumR d Γ (oldR d hn hm Γ f) = endpointSumR d Γ (newR d hn hm Γ f) := by
  have h' := sum_balanceR d hSq hC hE hSep hn hm Γ f
  omega

theorem other_oldR {A : NormalForm P} (z : At d.K A)
    (hc : z.index ≠ d.xC.index) (he : z.index ≠ d.xE.index) :
    (oldR d hn hm Γ f).rho .right z = 2+f.rho .right (d.originalViaE hE z hc he) := by
  have h := d.bc1.rankR_fixed (outerArity d hn) Γ (innerER d hm Γ f) z (d.middleE z hc) hc (d.middleE_get z hc)
  have h' := d.be0.rankR_fixed hm Γ f (d.middleE z hc) (d.originalViaE hE z hc he)
    (d.middleE_fixed hE z hc he) (d.originalViaE_get hE z hc he)
  exact h.trans ((congrArg (fun n : Nat => 1+n) h').trans (by omega))

include hSq hC in
theorem other_newR {A : NormalForm P} (z : At d.K A)
    (hc : z.index ≠ d.xC.index) (he : z.index ≠ d.xE.index) :
    (newR d hn hm Γ f).rho .right z = 2+f.rho .right (d.originalViaE hE z hc he) := by
  have h := d.be1.rankR_fixed (innerArity d hm) Γ (innerCR d hn Γ f) z (d.middleC z he) he (d.middleC_get z he)
  have h' := d.bc0.rankR_fixed hn Γ f (d.middleC z he) (d.originalViaE hE z hc he)
    (d.middleC_fixed hC z hc he) (d.other_c0_get hSq hC hE z hc he)
  exact h.trans ((congrArg (fun n : Nat => 1+n) h').trans (by omega))

end R
end W1.ContractionFrame
end DosenPetric.Reduced.Gentzen
