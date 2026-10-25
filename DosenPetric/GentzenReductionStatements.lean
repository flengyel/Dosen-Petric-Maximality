module

public import DosenPetric.GentzenStrictDescendants

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u} {C : NormalForm P} {Γ Δ Θ Λ U V : List (NormalForm P)}

/-- The complete left replacement conclusion, uniformly over containing
    addresses. This definition supplies no witness or mathematical premise. -/
def ReducesL (f : G P Γ (C::Δ)) (g : G P (C::Θ) Λ) (w : G P U V) (x : At U C) : Prop :=
  ∀ (a : ProofAddress g w), ReducibleL f g a x →
    ∃ h : G P U V, h.CutFree ∧ ofTerm h.denote=ofTerm w.denote ∧
      ∀ {I J : List (NormalForm P)} {v : G P I J} (b : ProofAddress h v) (y : At I C),
        ReducibleL f (a.replace h) ((a.inserted h).append b) y → v.rho .left y < w.rho .left x

/-- The separately typed right replacement conclusion. -/
def ReducesR (f : G P Γ (C::Δ)) (g : G P (C::Θ) Λ) (w : G P U V) (x : At V C) : Prop :=
  ∀ (a : ProofAddress f w), ReducibleR f g a x →
    ∃ h : G P U V, h.CutFree ∧ ofTerm h.denote=ofTerm w.denote ∧
      ∀ {I J : List (NormalForm P)} {v : G P I J} (b : ProofAddress h v) (y : At J C),
        ReducibleR (a.replace h) g ((a.inserted h).append b) y → v.rho .right y < w.rho .right x

end DosenPetric.Reduced.Gentzen
