module

public import DosenPetric.GentzenPositionalCuts
public import DosenPetric.GentzenPositionalThinning

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

namespace At

theorem toHead_thin_get (Γ Θ : List (NormalForm P)) (C : NormalForm P)
    {B : NormalForm P} (b : At (Γ ++ Θ) B) :
    (At.shift Γ (.here C Θ)).toHead.get ((Route.thin Γ Θ C).get b) =
      .there (b.cast (erase_shift Γ Θ C).symm) := by
  apply At.index_injective
  rw [toHead_get_index, thin_index, At.index_shift]
  simp only [index, Nat.add_zero, index_cast]
  unfold exchangeIndex
  by_cases h : b.index < Γ.length
  · rw [ite_eq_left h]
    split <;> (try split) <;> (try split) <;> omega
  · rw [ite_eq_right h]
    split <;> (try split) <;> (try split) <;> omega

/-- Moving an inserted thinning formula to the head preserves every surviving tag. -/
theorem toHead_thin_arrow (o : Op) (Γ Θ : List (NormalForm P)) (C : NormalForm P) :
    (side P o).comp ((At.shift Γ (.here C Θ)).toHead.arrow o)
        ((Route.thin Γ Θ C).sideArrow o) =
      (side P o).comp ((Route.thin [] (At.shift Γ (.here C Θ)).erase C).sideArrow o)
        (((Route.identity (At.shift Γ (.here C Θ)).erase).cast
          rfl (erase_shift Γ Θ C)).sideArrow o) := by
  let S := side P o
  apply side_ext o
  intro B b
  rw [S.assoc, Route.sideArrow_get, ExchangeScript.component,
    toHead_thin_get, S.assoc, Route.sideArrow_get, Route.sideArrow_get]
  apply congrArg (component o)
  apply At.index_injective
  rw [thin_index, Route.get_index_cast, Route.get_identity, index_cast]
  simp only [List.length_nil, Nat.not_lt_zero, ite_false, index, index_cast]

end At

namespace Route

theorem identity_sideArrow (o : Op) (Γ : List (NormalForm P)) :
    (identity Γ).sideArrow o = (side P o).id (fold o Γ) := by
  apply side_ext o
  intro A a
  rw [sideArrow_get, get_identity, (side P o).id_comp]

end Route
namespace G

theorem reindex_left_denote {Γ Γ' Δ : List (NormalForm P)} (h : Γ' = Γ)
    (f : G P Γ Δ) :
    ofTerm (f.reindex h.symm rfl).denote =
      comp (((Route.identity Γ').cast rfl h).sideArrow .conj) (ofTerm f.denote) := by
  cases h
  change ofTerm f.denote = comp ((Route.identity Γ).sideArrow .conj) (ofTerm f.denote)
  rw [Route.identity_sideArrow]
  exact (Laws.id_comp _).symm

theorem reindex_right_denote {Γ Δ Δ' : List (NormalForm P)} (h : Δ' = Δ)
    (f : G P Γ Δ) :
    ofTerm (f.reindex rfl h.symm).denote =
      comp (ofTerm f.denote) (((Route.identity Δ').cast rfl h).sideArrow .disj) := by
  cases h
  change ofTerm f.denote = comp (ofTerm f.denote) ((Route.identity Δ).sideArrow .disj)
  rw [Route.identity_sideArrow]
  exact (Laws.comp_id _).symm

theorem toHead_thinL_denote (Γ Θ Δ : List (NormalForm P)) (C : NormalForm P)
    (f : G P (Γ ++ Θ) Δ) :
    ofTerm ((At.shift Γ (.here C Θ)).toHead.left (G.thinL Γ Θ Δ C f)).denote =
      ofTerm (G.thinL [] (At.shift Γ (.here C Θ)).erase Δ C
        (f.reindex (At.erase_shift Γ Θ C).symm rfl)).denote := by
  rw [ExchangeScript.left_denote, G.denote_thinL, G.denote_thinL,
    reindex_left_denote (At.erase_shift Γ Θ C)]
  have he : comp ((At.shift Γ (.here C Θ)).toHead.arrow .conj)
      (ofTerm (Route.thin Γ Θ C).product) =
      comp (ofTerm (Route.thin [] (At.shift Γ (.here C Θ)).erase C).product)
        (((Route.identity (At.shift Γ (.here C Θ)).erase).cast
          rfl (At.erase_shift Γ Θ C)).sideArrow .conj) :=
    At.toHead_thin_arrow .conj Γ Θ C
  change comp _ (comp _ _) = comp _ (comp _ _)
  rw [← Laws.assoc, he, Laws.assoc]

theorem toHead_thinR_denote (Γ Δ Λ : List (NormalForm P)) (C : NormalForm P)
    (f : G P Γ (Δ ++ Λ)) :
    ofTerm ((At.shift Δ (.here C Λ)).toHead.right (G.thinR Γ Δ Λ C f)).denote =
      ofTerm (G.thinR Γ [] (At.shift Δ (.here C Λ)).erase C
        (f.reindex rfl (At.erase_shift Δ Λ C).symm)).denote := by
  rw [ExchangeScript.right_denote, G.denote_thinR, G.denote_thinR,
    reindex_right_denote (At.erase_shift Δ Λ C)]
  have he : comp (ofTerm (Route.thin Δ Λ C).coproduct)
      ((At.shift Δ (.here C Λ)).toHead.arrow .disj) =
      comp (((Route.identity (At.shift Δ (.here C Λ)).erase).cast
          rfl (At.erase_shift Δ Λ C)).sideArrow .disj)
        (ofTerm (Route.thin [] (At.shift Δ (.here C Λ)).erase C).coproduct) :=
    At.toHead_thin_arrow .disj Δ Λ C
  change comp (comp _ _) _ = comp (comp _ _) _
  rw [Laws.assoc, he, ← Laws.assoc]

end G
end DosenPetric.Reduced.Gentzen
