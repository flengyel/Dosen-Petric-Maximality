module

public import DosenPetric.GentzenBinaryMixSelected

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace BinaryMix

theorem native_swap {Γ Θ Δ Λ : List (NormalForm P)} (f : G P Γ Δ) (g : G P Θ Λ) :
    ofTerm (G.mix f g).denote =
      ofTerm ((swapWhole Γ Θ).left ((swapWhole Δ Λ).right (G.mix g f))).denote := by
  rw [ExchangeScript.left_denote,ExchangeScript.right_denote]
  change ofTerm (Rules.mix f.denote g.denote) =
    comp _ (comp (ofTerm (Rules.mix g.denote f.denote)) _)
  simp only [Rules.mix,ofTerm_comp,ofTerm_tensor,mix_term,Laws.assoc]
  have hi : comp ((swapWhole Γ Θ).arrow .conj) (ofTerm (append .conj Γ Θ).invTerm) =
      comp (ofTerm (append .conj Θ Γ).invTerm) (swap .conj (ante Θ) (ante Γ)) :=
    swapWhole_split .conj Γ Θ
  have ho : comp (ofTerm (append .disj Δ Λ).toTerm) ((swapWhole Δ Λ).arrow .disj) =
      comp (swap .disj (succ Δ) (succ Λ)) (ofTerm (append .disj Λ Δ).toTerm) :=
    swapWhole_split .disj Δ Λ
  erw [ho]
  rw [← Laws.assoc ((swapWhole Γ Θ).arrow .conj),hi]
  simp only [Laws.assoc]
  rw [← Laws.assoc (swap .conj (ante Θ) (ante Γ)),Laws.swap_nat]
  simp only [Laws.assoc]
  rw [← Laws.assoc (swap .conj (succ Λ) (succ Δ)),Laws.mix_swap]
  simp only [Laws.assoc]
  rw [← Laws.assoc (swap .disj (succ Λ) (succ Δ)),Laws.swap_swap,Laws.id_comp]

def swapProgram (F U : List (NormalForm P)) : StructuralProgram P (U ++ F) (F ++ U) :=
  (swapWhole F U).structural

theorem swapProgram_before (F U : List (NormalForm P)) {E : NormalForm P} (b : At F E) :
    (swapProgram F U).get (b.before U) = At.shift U b := by
  rw [swapProgram,ExchangeScript.structural_get,swapWhole_before]

theorem swapProgram_single {F U : List (NormalForm P)} {C : NormalForm P} (a : At F C) :
    (swapProgram F U).route.SingleFiber (At.shift U a) (a.before U) := by
  apply Route.singleFiber_of_unique
  · rw [StructuralProgram.route_get,swapProgram_before]
  · intro b hb
    rw [StructuralProgram.route_get,swapProgram,ExchangeScript.structural_get] at hb
    have he : (swapWhole F U).get b = (swapWhole F U).get (a.before U) := by
      rw [swapWhole_before]
      exact hb
    exact (swapWhole F U).injective b (a.before U) he

end BinaryMix
end DosenPetric.Reduced.Gentzen
