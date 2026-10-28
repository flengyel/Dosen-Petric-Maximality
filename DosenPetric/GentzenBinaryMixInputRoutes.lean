module

public import DosenPetric.GentzenBinaryMixRightDiagram

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace BinaryMix

theorem headShift_structural (F : List (NormalForm P)) {U : List (NormalForm P)}
    {C : NormalForm P} (a : At U C) (o : Op) :
    (LogicalDeletion.headShift F a).arrow o =
      (side P o).comp ((HeadRouting.front F a.erase C).arrow o)
        ((a.toHead.structural.prefixFixed F).arrow o) := by
  let S := side P o
  apply side_ext o
  intro E b
  rw [ExchangeScript.component,S.assoc,StructuralProgram.component]
  cases At.cases_append F U b with
  | inl hb =>
    obtain ⟨b,rfl⟩ := hb
    rw [StructuralProgram.prefixFixed_before,ExchangeScript.component,
      HeadRouting.front_before,LogicalDeletion.headShift_before]
  | inr hb =>
    obtain ⟨b,rfl⟩ := hb
    rw [StructuralProgram.prefixFixed_shift,ExchangeScript.structural_get,ExchangeScript.component]
    by_cases hi : b.index = a.index
    · have he := b.formula_eq a hi
      cases he
      have he : b = a := by apply At.index_injective; exact hi
      cases he
      rw [At.toHead_get,HeadRouting.front_head,LogicalDeletion.headShift_selected]
    · obtain ⟨b,rfl⟩ : ∃ b' : At a.erase E, b = a.retain b' :=
        ⟨a.remove b hi,(a.retain_remove b hi).symm⟩
      rw [At.toHead_get_retain,HeadRouting.front_tail,LogicalDeletion.headShift_fixed]

theorem fixed_prefix_mix {F U Δ Θ Λ : List (NormalForm P)}
    (p : StructuralProgram P F U) (f : G P U Δ) (g : G P Θ Λ) :
    ofTerm ((p.prefixFixed Θ).left (G.mix f g)).denote =
      ofTerm (G.mix (p.left f) g).denote := by
  rw [StructuralProgram.left_denote]
  change comp _ (ofTerm (Rules.mix f.denote g.denote)) =
    ofTerm (Rules.mix (p.left f).denote g.denote)
  simp only [Rules.mix,ofTerm_comp,ofTerm_tensor,mix_term]
  rw [StructuralProgram.left_denote]
  have he : comp ((p.prefixFixed Θ).arrow .conj) (ofTerm (append .conj Θ U).invTerm) =
      comp (ofTerm (append .conj Θ F).invTerm)
        (tensor .conj (id (ante Θ)) (p.arrow .conj)) := p.prefixFixed_split .conj Θ
  rw [← Laws.assoc,he]
  simp only [Laws.assoc]
  rw [← Laws.assoc (tensor .conj (id (ante Θ)) (p.arrow .conj)),Laws.tensor_comp,Laws.id_comp]

theorem headShift_mix {Γ Θ Δ Λ : List (NormalForm P)} {C : NormalForm P}
    (f : G P Γ Δ) (a : At Γ C) (g : G P Θ Λ) :
    ofTerm ((LogicalDeletion.headShift Θ a).left (G.mix f g)).denote =
      ofTerm ((HeadRouting.front Θ a.erase C).left (G.mix (a.toHead.left f) g)).denote := by
  rw [ExchangeScript.left_denote,headShift_structural]
  have he := fixed_prefix_mix a.toHead.structural f g
  rw [StructuralProgram.left_denote] at he
  change comp (comp ((HeadRouting.front Θ a.erase C).arrow .conj)
    ((a.toHead.structural.prefixFixed Θ).arrow .conj)) (ofTerm (G.mix f g).denote) = _
  rw [Laws.assoc,he,ExchangeScript.left_denote]
  have ha : ofTerm (a.toHead.structural.left f).denote = ofTerm (a.toHead.left f).denote := by
    rw [StructuralProgram.left_denote,ExchangeScript.left_denote,ExchangeScript.structural_arrow]
  have hh : ofTerm (Rules.mix (a.toHead.structural.left f).denote g.denote) =
      ofTerm (Rules.mix (a.toHead.left f).denote g.denote) := Rules.mix_congr ha rfl
  change comp _ (ofTerm (Rules.mix (a.toHead.structural.left f).denote g.denote)) = _
  rw [hh]
  rfl

end BinaryMix
end DosenPetric.Reduced.Gentzen
