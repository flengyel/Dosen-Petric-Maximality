module

public import DosenPetric.GentzenDisjointCommutation
public import DosenPetric.GentzenDisjointFixed

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

theorem sum_transport_one {α β : Type u} (xs : List α) (ys : List β) (φ : α → β)
    (r : α → Nat) (s : β → Nat) (hy : ys = xs.map φ)
    (h : ∀ a, a ∈ xs → s (φ a) = 1+r a) :
    (ys.map s).sum = (xs.map r).sum+xs.length := by
  rw [hy,List.map_map]
  change (xs.map (fun a => s (φ a))).sum = _
  have he : xs.map (fun a => s (φ a)) = xs.map (fun a => 1+r a) := List.map_congr_left h
  rw [he,G.sum_map_one_add]

namespace W1.DisjointContraction
variable (d : Disjoint.Data P) (hn : 2 ≤ d.outer0.length) (hm : 2 ≤ d.es.length)

section L
variable (Δ : List (NormalForm P)) (f : G P d.F Δ)

def LCL := d.bc0.rankL hn Δ f
def LEL := d.be0.rankL hm Δ f

theorem oldC_contractionL : d.bc1.rankL (outerArity d hn) Δ (innerEL d hm Δ f) = LCL d hn Δ f+d.outer0.length := by
  have h₀ := d.bc0.rankL_sum hn Δ f
  have h₁ := d.bc1.rankL_sum (outerArity d hn) Δ (innerEL d hm Δ f)
  have hs : (d.selectedC1.map (fun a => (innerEL d hm Δ f).rho .left a)).sum =
      (d.selectedC0.map (fun a => f.rho .left a)).sum+d.selectedC0.length := by
    apply sum_transport_one _ _ d.e0.get _ _ d.selectedC_transport
    intro a ha
    exact d.be0.rankL_fixed hm Δ f (d.e0.get a) a (d.selectedC0_parametric a ha) rfl
  have hl := d.selectedC0_length
  change LCL d hn Δ f = 1+(d.selectedC0.map (fun a => f.rho .left a)).sum at h₀
  change d.bc1.rankL (outerArity d hn) Δ (innerEL d hm Δ f) =
    1+(d.selectedC1.map (fun a => (innerEL d hm Δ f).rho .left a)).sum at h₁
  omega

theorem newE_contractionL : d.be1.rankL hm Δ (innerCL d hn Δ f) = LEL d hm Δ f+d.es.length := by
  have h₀ := d.be0.rankL_sum hm Δ f
  have h₁ := d.be1.rankL_sum hm Δ (innerCL d hn Δ f)
  have hs : (d.selectedE1.map (fun a => (innerCL d hn Δ f).rho .left a)).sum =
      (d.selectedE0.map (fun a => f.rho .left a)).sum+d.selectedE0.length := by
    apply sum_transport_one _ _ d.c0.get _ _ d.selectedE_transport
    intro a ha
    exact d.bc0.rankL_fixed hn Δ f (d.c0.get a) a (d.selectedE0_parametric a ha) rfl
  have hl := d.selectedE0_length
  change LEL d hm Δ f = 1+(d.selectedE0.map (fun a => f.rho .left a)).sum at h₀
  change d.be1.rankL hm Δ (innerCL d hn Δ f) =
    1+(d.selectedE1.map (fun a => (innerCL d hn Δ f).rho .left a)).sum at h₁
  omega

theorem old_xCL : (oldL d hn hm Δ f).rho .left d.xC = LCL d hn Δ f+d.outer0.length :=
  (d.bc1.rankL_keep (outerArity d hn) Δ _).trans (oldC_contractionL ..)

theorem new_xEL : (newL d hn hm Δ f).rho .left d.xE = LEL d hm Δ f+d.es.length :=
  (d.be1.rankL_keep hm Δ _).trans (newE_contractionL ..)

theorem new_xCL : (newL d hn hm Δ f).rho .left d.xC = LCL d hn Δ f+1 := by
  have h := d.be1.rankL_fixed hm Δ (innerCL d hn Δ f) d.xC d.keepC0
    (by change d.xC.index ≠ d.xE.index; have h := d.retained_order; omega) d.e1_keepC0
  have h' := d.bc0.rankL_keep hn Δ f
  change (newL d hn hm Δ f).rho .left d.xC = 1+(innerCL d hn Δ f).rho .left d.keepC0 at h
  exact h.trans ((congrArg (fun n : Nat => 1+n) h').trans (Nat.add_comm ..))

theorem old_xEL : (oldL d hn hm Δ f).rho .left d.xE = LEL d hm Δ f+1 := by
  have h := d.bc1.rankL_fixed (outerArity d hn) Δ (innerEL d hm Δ f) d.xE d.keepE0
    (by change d.xE.index ≠ d.xC.index; have h := d.retained_order; omega) d.c1_keepE0
  have h' := d.be0.rankL_keep hm Δ f
  change (oldL d hn hm Δ f).rho .left d.xE = 1+(innerEL d hm Δ f).rho .left d.keepE0 at h
  exact h.trans ((congrArg (fun n : Nat => 1+n) h').trans (Nat.add_comm ..))

theorem C_balanceL : (oldL d hn hm Δ f).rho .left d.xC+1 = (newL d hn hm Δ f).rho .left d.xC+d.outer0.length := by
  have h0 := old_xCL d hn hm Δ f
  have h1 := new_xCL d hn hm Δ f
  omega

theorem E_balanceL : (newL d hn hm Δ f).rho .left d.xE+1 = (oldL d hn hm Δ f).rho .left d.xE+d.es.length := by
  have h0 := old_xEL d hn hm Δ f
  have h1 := new_xEL d hn hm Δ f
  omega

theorem C_decreasesL : (newL d hn hm Δ f).rho .left d.xC < (oldL d hn hm Δ f).rho .left d.xC := by
  have h0 := old_xCL d hn hm Δ f
  have h1 := new_xCL d hn hm Δ f
  omega

theorem E_increasesL : (oldL d hn hm Δ f).rho .left d.xE < (newL d hn hm Δ f).rho .left d.xE := by
  have h0 := old_xEL d hn hm Δ f
  have h1 := new_xEL d hn hm Δ f
  omega

theorem C_subterm_ltL : LCL d hn Δ f < (oldL d hn hm Δ f).rho .left d.xC := by
  have h0 := old_xCL d hn hm Δ f
  omega

theorem E_subterm_ltL : LEL d hm Δ f < (newL d hn hm Δ f).rho .left d.xE := by
  have h0 := new_xEL d hn hm Δ f
  omega

def endpointSumL (g : G P d.K Δ) : Nat := g.rho .left d.xC+g.rho .left d.xE

theorem sum_balanceL : endpointSumL d Δ (oldL d hn hm Δ f)+d.es.length =
    endpointSumL d Δ (newL d hn hm Δ f)+d.outer0.length := by
  change (oldL d hn hm Δ f).rho .left d.xC+(oldL d hn hm Δ f).rho .left d.xE+d.es.length =
    (newL d hn hm Δ f).rho .left d.xC+(newL d hn hm Δ f).rho .left d.xE+d.outer0.length
  have h₀ := old_xCL d hn hm Δ f
  have h₁ := old_xEL d hn hm Δ f
  have h₂ := new_xCL d hn hm Δ f
  have h₃ := new_xEL d hn hm Δ f
  omega

theorem sum_eq_of_arity_eqL (h : d.outer0.length = d.es.length) :
    endpointSumL d Δ (oldL d hn hm Δ f) = endpointSumL d Δ (newL d hn hm Δ f) := by
  have h' := sum_balanceL d hn hm Δ f
  omega

theorem other_oldL {A : NormalForm P} (z : At d.K A)
    (hc : z.index ≠ d.xC.index) (he : z.index ≠ d.xE.index) :
    (oldL d hn hm Δ f).rho .left z = 2+f.rho .left (d.originalViaE z hc he) := by
  have h := d.bc1.rankL_fixed (outerArity d hn) Δ (innerEL d hm Δ f) z (d.middleE z hc) hc (d.middleE_get z hc)
  have h' := d.be0.rankL_fixed hm Δ f (d.middleE z hc) (d.originalViaE z hc he)
    (d.middleE_fixed z hc he) (d.originalViaE_get z hc he)
  exact h.trans ((congrArg (fun n : Nat => 1+n) h').trans (by omega))

theorem other_newL {A : NormalForm P} (z : At d.K A)
    (hc : z.index ≠ d.xC.index) (he : z.index ≠ d.xE.index) :
    (newL d hn hm Δ f).rho .left z = 2+f.rho .left (d.originalViaE z hc he) := by
  have h := d.be1.rankL_fixed hm Δ (innerCL d hn Δ f) z (d.middleC z he) he (d.middleC_get z he)
  have h' := d.bc0.rankL_fixed hn Δ f (d.middleC z he) (d.originalViaE z hc he)
    (d.middleC_fixed z hc he) (d.other_c0_get z hc he)
  exact h.trans ((congrArg (fun n : Nat => 1+n) h').trans (by omega))

end L

section R
variable (Γ : List (NormalForm P)) (f : G P Γ d.F)

def LCR := d.bc0.rankR hn Γ f
def LER := d.be0.rankR hm Γ f

theorem oldC_contractionR : d.bc1.rankR (outerArity d hn) Γ (innerER d hm Γ f) = LCR d hn Γ f+d.outer0.length := by
  have h₀ := d.bc0.rankR_sum hn Γ f
  have h₁ := d.bc1.rankR_sum (outerArity d hn) Γ (innerER d hm Γ f)
  have hs : (d.selectedC1.map (fun a => (innerER d hm Γ f).rho .right a)).sum =
      (d.selectedC0.map (fun a => f.rho .right a)).sum+d.selectedC0.length := by
    apply sum_transport_one _ _ d.e0.get _ _ d.selectedC_transport
    intro a ha
    exact d.be0.rankR_fixed hm Γ f (d.e0.get a) a (d.selectedC0_parametric a ha) rfl
  have hl := d.selectedC0_length
  change LCR d hn Γ f = 1+(d.selectedC0.map (fun a => f.rho .right a)).sum at h₀
  change d.bc1.rankR (outerArity d hn) Γ (innerER d hm Γ f) =
    1+(d.selectedC1.map (fun a => (innerER d hm Γ f).rho .right a)).sum at h₁
  omega

theorem newE_contractionR : d.be1.rankR hm Γ (innerCR d hn Γ f) = LER d hm Γ f+d.es.length := by
  have h₀ := d.be0.rankR_sum hm Γ f
  have h₁ := d.be1.rankR_sum hm Γ (innerCR d hn Γ f)
  have hs : (d.selectedE1.map (fun a => (innerCR d hn Γ f).rho .right a)).sum =
      (d.selectedE0.map (fun a => f.rho .right a)).sum+d.selectedE0.length := by
    apply sum_transport_one _ _ d.c0.get _ _ d.selectedE_transport
    intro a ha
    exact d.bc0.rankR_fixed hn Γ f (d.c0.get a) a (d.selectedE0_parametric a ha) rfl
  have hl := d.selectedE0_length
  change LER d hm Γ f = 1+(d.selectedE0.map (fun a => f.rho .right a)).sum at h₀
  change d.be1.rankR hm Γ (innerCR d hn Γ f) =
    1+(d.selectedE1.map (fun a => (innerCR d hn Γ f).rho .right a)).sum at h₁
  omega

theorem old_xCR : (oldR d hn hm Γ f).rho .right d.xC = LCR d hn Γ f+d.outer0.length :=
  (d.bc1.rankR_keep (outerArity d hn) Γ _).trans (oldC_contractionR ..)

theorem new_xER : (newR d hn hm Γ f).rho .right d.xE = LER d hm Γ f+d.es.length :=
  (d.be1.rankR_keep hm Γ _).trans (newE_contractionR ..)

theorem new_xCR : (newR d hn hm Γ f).rho .right d.xC = LCR d hn Γ f+1 := by
  have h := d.be1.rankR_fixed hm Γ (innerCR d hn Γ f) d.xC d.keepC0
    (by change d.xC.index ≠ d.xE.index; have h := d.retained_order; omega) d.e1_keepC0
  have h' := d.bc0.rankR_keep hn Γ f
  change (newR d hn hm Γ f).rho .right d.xC = 1+(innerCR d hn Γ f).rho .right d.keepC0 at h
  exact h.trans ((congrArg (fun n : Nat => 1+n) h').trans (Nat.add_comm ..))

theorem old_xER : (oldR d hn hm Γ f).rho .right d.xE = LER d hm Γ f+1 := by
  have h := d.bc1.rankR_fixed (outerArity d hn) Γ (innerER d hm Γ f) d.xE d.keepE0
    (by change d.xE.index ≠ d.xC.index; have h := d.retained_order; omega) d.c1_keepE0
  have h' := d.be0.rankR_keep hm Γ f
  change (oldR d hn hm Γ f).rho .right d.xE = 1+(innerER d hm Γ f).rho .right d.keepE0 at h
  exact h.trans ((congrArg (fun n : Nat => 1+n) h').trans (Nat.add_comm ..))

theorem C_balanceR : (oldR d hn hm Γ f).rho .right d.xC+1 = (newR d hn hm Γ f).rho .right d.xC+d.outer0.length := by
  have h0 := old_xCR d hn hm Γ f
  have h1 := new_xCR d hn hm Γ f
  omega

theorem E_balanceR : (newR d hn hm Γ f).rho .right d.xE+1 = (oldR d hn hm Γ f).rho .right d.xE+d.es.length := by
  have h0 := old_xER d hn hm Γ f
  have h1 := new_xER d hn hm Γ f
  omega

theorem C_decreasesR : (newR d hn hm Γ f).rho .right d.xC < (oldR d hn hm Γ f).rho .right d.xC := by
  have h0 := old_xCR d hn hm Γ f
  have h1 := new_xCR d hn hm Γ f
  omega

theorem E_increasesR : (oldR d hn hm Γ f).rho .right d.xE < (newR d hn hm Γ f).rho .right d.xE := by
  have h0 := old_xER d hn hm Γ f
  have h1 := new_xER d hn hm Γ f
  omega

theorem C_subterm_ltR : LCR d hn Γ f < (oldR d hn hm Γ f).rho .right d.xC := by
  have h0 := old_xCR d hn hm Γ f
  omega

theorem E_subterm_ltR : LER d hm Γ f < (newR d hn hm Γ f).rho .right d.xE := by
  have h0 := new_xER d hn hm Γ f
  omega

def endpointSumR (g : G P Γ d.K) : Nat := g.rho .right d.xC+g.rho .right d.xE

theorem sum_balanceR : endpointSumR d Γ (oldR d hn hm Γ f)+d.es.length =
    endpointSumR d Γ (newR d hn hm Γ f)+d.outer0.length := by
  change (oldR d hn hm Γ f).rho .right d.xC+(oldR d hn hm Γ f).rho .right d.xE+d.es.length =
    (newR d hn hm Γ f).rho .right d.xC+(newR d hn hm Γ f).rho .right d.xE+d.outer0.length
  have h₀ := old_xCR d hn hm Γ f
  have h₁ := old_xER d hn hm Γ f
  have h₂ := new_xCR d hn hm Γ f
  have h₃ := new_xER d hn hm Γ f
  omega

theorem sum_eq_of_arity_eqR (h : d.outer0.length = d.es.length) :
    endpointSumR d Γ (oldR d hn hm Γ f) = endpointSumR d Γ (newR d hn hm Γ f) := by
  have h' := sum_balanceR d hn hm Γ f
  omega

theorem other_oldR {A : NormalForm P} (z : At d.K A)
    (hc : z.index ≠ d.xC.index) (he : z.index ≠ d.xE.index) :
    (oldR d hn hm Γ f).rho .right z = 2+f.rho .right (d.originalViaE z hc he) := by
  have h := d.bc1.rankR_fixed (outerArity d hn) Γ (innerER d hm Γ f) z (d.middleE z hc) hc (d.middleE_get z hc)
  have h' := d.be0.rankR_fixed hm Γ f (d.middleE z hc) (d.originalViaE z hc he)
    (d.middleE_fixed z hc he) (d.originalViaE_get z hc he)
  exact h.trans ((congrArg (fun n : Nat => 1+n) h').trans (by omega))

theorem other_newR {A : NormalForm P} (z : At d.K A)
    (hc : z.index ≠ d.xC.index) (he : z.index ≠ d.xE.index) :
    (newR d hn hm Γ f).rho .right z = 2+f.rho .right (d.originalViaE z hc he) := by
  have h := d.be1.rankR_fixed hm Γ (innerCR d hn Γ f) z (d.middleC z he) he (d.middleC_get z he)
  have h' := d.bc0.rankR_fixed hn Γ f (d.middleC z he) (d.originalViaE z hc he)
    (d.middleC_fixed z hc he) (d.other_c0_get z hc he)
  exact h.trans ((congrArg (fun n : Nat => 1+n) h').trans (by omega))

end R
end W1.DisjointContraction
end DosenPetric.Reduced.Gentzen
