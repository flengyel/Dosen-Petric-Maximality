module

public import DosenPetric.GentzenSelectedExchangeBlocked
public import DosenPetric.GentzenContextNormalizationLaws

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace PositionalCut

/-- Simultaneous clean representatives at the original selected sequents.
This normalization has no selected-rank bound. -/
theorem clean_premises {Γ Δ Θ Λ : List (NormalForm P)} {C : NormalForm P}
    (f : G P Γ Δ) (x : At Δ C) (g : G P Θ Λ) (y : At Θ C)
    (hf : f.CutFree) (hg : g.CutFree) :
    ∃ (f' : G P Γ Δ) (g' : G P Θ Λ), Clean f' x g' y ∧
      ofTerm f'.denote = ofTerm f.denote ∧ ofTerm g'.denote = ofTerm g.denote := by
  have hxf : (x.toHead.right f).CutFree := by
    change (x.toHead.right f).cutCount = 0
    rw [ExchangeScript.right_count]
    exact hf
  have hyg : (y.toHead.left g).CutFree := by
    change (y.toHead.left g).cutCount = 0
    rw [ExchangeScript.left_count]
    exact hg
  obtain ⟨a,b,ht,aa,ab,ea,eb,ba,bb⟩ := clean_cut_premises
    (x.toHead.right f) (y.toHead.left g) ⟨hxf,hyg⟩
  let f' := x.toHead.inverse.right a
  let g' := y.toHead.inverse.left b
  have hix : x.toHead.inverse.get (.here C x.erase) = x := by
    rw [← x.toHead_get]
    exact x.toHead.inverse_get x
  have hiy : y.toHead.inverse.get (.here C y.erase) = y := by
    rw [← y.toHead_get]
    exact y.toHead.inverse_get y
  refine ⟨f',g',⟨?_,?_,?_,?_,?_,?_⟩,?_,?_⟩
  · change (x.toHead.inverse.right a).cutCount = 0
    rw [ExchangeScript.right_count]
    exact ht.1
  · change (y.toHead.inverse.left b).cutCount = 0
    rw [ExchangeScript.left_count]
    exact ht.2
  · exact (ExchangeScript.right_atomized _ _).mpr aa
  · exact (ExchangeScript.left_atomized _ _).mpr ab
  · have hh : AllBlockedAt f' .right (x.toHead.inverse.get (.here C x.erase)) :=
      x.toHead.inverse.blocked_right a (.here C x.erase)
      ((allBlockedAt_head_right a).mpr ba)
    intro U V w addr z hz hl
    apply hh addr z _ hl
    rw [hix]
    exact hz
  · have hh : AllBlockedAt g' .left (y.toHead.inverse.get (.here C y.erase)) :=
      y.toHead.inverse.blocked_left b (.here C y.erase)
      ((allBlockedAt_head_left b).mpr bb)
    intro U V w addr z hz hl
    apply hh addr z _ hl
    rw [hiy]
    exact hz
  · change ofTerm (x.toHead.inverse.right a).denote = ofTerm f.denote
    rw [ExchangeScript.right_denote, ea, ExchangeScript.right_denote, Laws.assoc]
    have he : comp (x.toHead.arrow .disj) (x.toHead.inverse.arrow .disj) = id (succ Δ) :=
      x.toHead.inverse_arrow .disj
    rw [he, Laws.comp_id]
  · change ofTerm (y.toHead.inverse.left b).denote = ofTerm g.denote
    rw [ExchangeScript.left_denote, eb, ExchangeScript.left_denote, ← Laws.assoc]
    have he : comp (y.toHead.inverse.arrow .conj) (y.toHead.arrow .conj) = id (ante Θ) :=
      y.toHead.inverse_arrow .conj
    rw [he, Laws.id_comp]

end PositionalCut
end DosenPetric.Reduced.Gentzen
