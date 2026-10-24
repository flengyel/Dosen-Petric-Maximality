module

public import DosenPetric.GentzenContractionBlocks
public import DosenPetric.GentzenExchangeEmbeddings

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

namespace Route
theorem get_cast {Γ Δ Γ' Δ' : List (NormalForm P)} (hΓ : Γ = Γ') (hΔ : Δ = Δ')
    (w : Route Γ Δ) {A : NormalForm P} (a : At Δ' A) :
    (w.cast hΓ hΔ).get a = (w.get (a.cast hΔ.symm)).cast hΓ := by
  cases hΓ; cases hΔ; rfl

def exchange (Γ X Y Θ : List (NormalForm P)) : Route (Γ++Y++X++Θ) (Γ++X++Y++Θ) :=
  (Route.identity (Γ++X++Y++Θ)).map (fun a => a.swapBlocks Γ X Y Θ)

theorem exchange_get (Γ X Y Θ : List (NormalForm P)) {A : NormalForm P}
    (a : At (Γ++X++Y++Θ) A) : (exchange Γ X Y Θ).get a = a.swapBlocks Γ X Y Θ := by
  rw [exchange,get_map,get_identity]

theorem exchange_product (Γ X Y Θ : List (NormalForm P)) :
    ofTerm (exchange Γ X Y Θ).product = ofTerm (Gentzen.exchange .conj Γ X Y Θ).invTerm := by
  apply product_positions
  intro A a
  rw [product_get,exchange_get,exchangeL_projection]

theorem exchange_coproduct (Γ X Y Θ : List (NormalForm P)) :
    ofTerm (exchange Γ X Y Θ).coproduct = ofTerm (Gentzen.exchange .disj Γ X Y Θ).toTerm := by
  apply coproduct_positions
  intro A a
  rw [coproduct_get,exchange_get,exchangeR_injection]
end Route

namespace UnaryCast
variable {F U : List (NormalForm P)}

def thinL (Γ Θ : List (NormalForm P)) (C : NormalForm P)
    (hF : Γ++Θ = F) (hU : Γ++C::Θ = U) (Δ : List (NormalForm P)) (f : G P F Δ) : G P U Δ :=
  (G.thinL Γ Θ Δ C (f.reindex hF.symm rfl)).reindex hU rfl
def thinR (Δ Λ : List (NormalForm P)) (C : NormalForm P)
    (hF : Δ++Λ = F) (hU : Δ++C::Λ = U) (Γ : List (NormalForm P)) (f : G P Γ F) : G P Γ U :=
  (G.thinR Γ Δ Λ C (f.reindex rfl hF.symm)).reindex rfl hU

theorem thinL_denote (Γ Θ : List (NormalForm P)) (C : NormalForm P)
    (hF : Γ++Θ = F) (hU : Γ++C::Θ = U) (Δ : List (NormalForm P)) (f : G P F Δ) :
    ofTerm (thinL Γ Θ C hF hU Δ f).denote =
      comp (ofTerm ((Route.thin Γ Θ C).cast hU hF).product) (ofTerm f.denote) := by
  cases hU; cases hF; rfl
theorem thinR_denote (Δ Λ : List (NormalForm P)) (C : NormalForm P)
    (hF : Δ++Λ = F) (hU : Δ++C::Λ = U) (Γ : List (NormalForm P)) (f : G P Γ F) :
    ofTerm (thinR Δ Λ C hF hU Γ f).denote =
      comp (ofTerm f.denote) (ofTerm ((Route.thin Δ Λ C).cast hU hF).coproduct) := by
  cases hU; cases hF; rfl

theorem thinL_embedded (Γ Θ : List (NormalForm P)) (C : NormalForm P)
    (hF : Γ++Θ = F) (hU : Γ++C::Θ = U) (Δ : List (NormalForm P)) (f : G P F Δ)
    {A : NormalForm P} (a : At F A) :
    (thinL Γ Θ C hF hU Δ f).rho .left (((Route.thin Γ Θ C).cast hU hF).get a) =
      1+f.rho .left a := by
  cases hU; cases hF; exact G.rho_thinL_embedded Γ Θ Δ C f a
theorem thinR_embedded (Δ Λ : List (NormalForm P)) (C : NormalForm P)
    (hF : Δ++Λ = F) (hU : Δ++C::Λ = U) (Γ : List (NormalForm P)) (f : G P Γ F)
    {A : NormalForm P} (a : At F A) :
    (thinR Δ Λ C hF hU Γ f).rho .right (((Route.thin Δ Λ C).cast hU hF).get a) =
      1+f.rho .right a := by
  cases hU; cases hF; exact G.rho_thinR_embedded Γ Δ Λ C f a

theorem thinL_principal (Γ Θ : List (NormalForm P)) (C : NormalForm P)
    (hF : Γ++Θ = F) (hU : Γ++C::Θ = U) (Δ : List (NormalForm P)) (f : G P F Δ) :
    (thinL Γ Θ C hF hU Δ f).rho .left ((At.shift Γ (.here C Θ)).cast hU) = 1 := by
  cases hU; cases hF; exact G.rho_thinL_principal Γ Θ Δ C f
theorem thinR_principal (Δ Λ : List (NormalForm P)) (C : NormalForm P)
    (hF : Δ++Λ = F) (hU : Δ++C::Λ = U) (Γ : List (NormalForm P)) (f : G P Γ F) :
    (thinR Δ Λ C hF hU Γ f).rho .right ((At.shift Δ (.here C Λ)).cast hU) = 1 := by
  cases hU; cases hF; exact G.rho_thinR_principal Γ Δ Λ C f

def exchangeL (Γ X Y Θ : List (NormalForm P)) (hF : Γ++X++Y++Θ = F)
    (hU : Γ++Y++X++Θ = U) (Δ : List (NormalForm P)) (f : G P F Δ) : G P U Δ :=
  (G.exchangeL Γ X Y Θ Δ (f.reindex hF.symm rfl)).reindex hU rfl
def exchangeR (Δ X Y Λ : List (NormalForm P)) (hF : Δ++X++Y++Λ = F)
    (hU : Δ++Y++X++Λ = U) (Γ : List (NormalForm P)) (f : G P Γ F) : G P Γ U :=
  (G.exchangeR Γ Δ X Y Λ (f.reindex rfl hF.symm)).reindex rfl hU

theorem exchangeL_denote (Γ X Y Θ : List (NormalForm P)) (hF : Γ++X++Y++Θ = F)
    (hU : Γ++Y++X++Θ = U) (Δ : List (NormalForm P)) (f : G P F Δ) :
    ofTerm (exchangeL Γ X Y Θ hF hU Δ f).denote =
      comp (ofTerm ((Route.exchange Γ X Y Θ).cast hU hF).product) (ofTerm f.denote) := by
  cases hU; cases hF
  change comp (ofTerm (Gentzen.exchange .conj Γ X Y Θ).invTerm) (ofTerm f.denote) =
    comp (ofTerm (Route.exchange Γ X Y Θ).product) (ofTerm f.denote)
  rw [Route.exchange_product]
theorem exchangeR_denote (Δ X Y Λ : List (NormalForm P)) (hF : Δ++X++Y++Λ = F)
    (hU : Δ++Y++X++Λ = U) (Γ : List (NormalForm P)) (f : G P Γ F) :
    ofTerm (exchangeR Δ X Y Λ hF hU Γ f).denote =
      comp (ofTerm f.denote) (ofTerm ((Route.exchange Δ X Y Λ).cast hU hF).coproduct) := by
  cases hU; cases hF
  change comp (ofTerm f.denote) (ofTerm (Gentzen.exchange .disj Δ X Y Λ).toTerm) =
    comp (ofTerm f.denote) (ofTerm (Route.exchange Δ X Y Λ).coproduct)
  rw [Route.exchange_coproduct]

theorem exchangeL_embedded (Γ X Y Θ : List (NormalForm P)) (hF : Γ++X++Y++Θ = F)
    (hU : Γ++Y++X++Θ = U) (Δ : List (NormalForm P)) (f : G P F Δ)
    {A : NormalForm P} (a : At F A) :
    (exchangeL Γ X Y Θ hF hU Δ f).rho .left (((Route.exchange Γ X Y Θ).cast hU hF).get a) =
      1+f.rho .left a := by
  cases hU; cases hF
  exact (congrArg (fun x => (G.exchangeL Γ X Y Θ Δ f).rho .left x)
    (Route.exchange_get Γ X Y Θ a)).trans (G.rho_exchangeL_embedded Γ X Y Θ Δ f a)
theorem exchangeR_embedded (Δ X Y Λ : List (NormalForm P)) (hF : Δ++X++Y++Λ = F)
    (hU : Δ++Y++X++Λ = U) (Γ : List (NormalForm P)) (f : G P Γ F)
    {A : NormalForm P} (a : At F A) :
    (exchangeR Δ X Y Λ hF hU Γ f).rho .right (((Route.exchange Δ X Y Λ).cast hU hF).get a) =
      1+f.rho .right a := by
  cases hU; cases hF
  exact (congrArg (fun x => (G.exchangeR Γ Δ X Y Λ f).rho .right x)
    (Route.exchange_get Δ X Y Λ a)).trans (G.rho_exchangeR_embedded Γ Δ X Y Λ f a)

end UnaryCast
end DosenPetric.Reduced.Gentzen
