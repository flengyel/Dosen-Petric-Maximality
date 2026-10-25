module

public import DosenPetric.GentzenNonemptyRightRanks
public import DosenPetric.GentzenSingletonRightRegression

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.W4.NonemptyRight
universe u
variable {P : Type u} (d : Gentzen.SelectedLogical.Data P .disj)
variable (hn : 1 ≤ d.gs.length) (Γ : List (NormalForm P)) (f : G P Γ d.F)

/-- Nonempty-parametric terminal right W4, including one parametric copy and
    one fresh compound, at an arbitrary actual containing address. -/
theorem addressed_right {Ξ Δ Θ Λ : List (NormalForm P)} {root : G P Ξ (d.C::Δ)}
    {cutRight : G P (d.C::Θ) Λ} (a : ProofAddress root (old d hn Γ f))
    (hr : ReducibleR root cutRight a d.x) :
    (repair d hn Γ f).CutFree ∧
    ofTerm (repair d hn Γ f).denote = ofTerm (old d hn Γ f).denote ∧
    ofTerm (a.replace (repair d hn Γ f)).denote = ofTerm root.denote ∧
    ∀ {I J : List (NormalForm P)} {v : G P I J}
      (b : ProofAddress (repair d hn Γ f) v) (y : At J d.C),
      ReducibleR (a.replace (repair d hn Γ f)) cutRight ((a.inserted _).append b) y →
        v.rho .right y < (old d hn Γ f).rho .right d.x := by
  have he:=denote d hn Γ f
  have hc : f.CutFree := by
    have hc:=hr.cutFree
    change (old d hn Γ f).cutCount=0 at hc
    rw [old_count] at hc
    exact hc
  refine ⟨(cutFree d hn Γ f).mpr hc,he,a.replace_denote _ he,?_⟩
  intro I J v b y hv
  obtain ⟨z,hz,ha⟩ := (a.replacement_cluster_iff (repair d hn Γ f) b .right
    (.here d.C Δ) y).mp hv.2.1.1
  have hx : z=d.x := hr.entry_unique z ha
  cases hx
  have hb := (repair_bound d hn Γ f).bound b d.x rfl y hz hv.2.1.2 hv.2.2.1
  have ho:=inner_lt_old d hn Γ f
  omega

namespace Examples
abbrev data : Gentzen.SelectedLogical.Data Empty .disj := ⟨.bot,.bot,[[]],[]⟩
theorem native_old : old data (Nat.le_refl 1) [.bot] SingletonRightRegression.premise =
    SingletonRightRegression.old := rfl
theorem singleton_inner : inner data (Nat.le_refl 1) [.bot] SingletonRightRegression.premise =
    SingletonRightRegression.premise := rfl

theorem native_replacement :
    (repair data (Nat.le_refl 1) [.bot] SingletonRightRegression.premise).CutFree ∧
    ofTerm (repair data (Nat.le_refl 1) [.bot] SingletonRightRegression.premise).denote =
      ofTerm SingletonRightRegression.old.denote ∧
    ∀ {I J : List (NormalForm Empty)} {v : G Empty I J}
      (b : ProofAddress (repair data (Nat.le_refl 1) [.bot] SingletonRightRegression.premise) v)
      (y : At J SingletonRightRegression.C),
      ReducibleR (repair data (Nat.le_refl 1) [.bot] SingletonRightRegression.premise)
        SingletonRightRegression.other b y →
        v.rho .right y < SingletonRightRegression.old.rho .right (.here _ []) := by
  have h:=addressed_right data (Nat.le_refl 1) [.bot] SingletonRightRegression.premise
    ProofAddress.root SingletonRightRegression.old_reducible
  refine ⟨h.1,h.2.1,?_⟩
  intro I J v b y hr
  apply h.2.2.2 b y
  simpa only [ProofAddress.replace,ProofAddress.inserted,ProofAddress.root_append] using hr
end Examples

end DosenPetric.Reduced.Gentzen.W4.NonemptyRight
