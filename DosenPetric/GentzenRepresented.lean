module

public import DosenPetric.GentzenContractions

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

/-- Existence of a proof with cuts; no choice or quotient translation is asserted. -/
def Represented {A B : NormalForm P} (f : Hom A B) : Prop :=
  ∃ g : G P [A] [B], decode g.denote = f

namespace Represented

theorem identity (A : NormalForm P) : Represented (id A) := ⟨G.identityNF A, G.identityNF_value A⟩
theorem zero (A : NormalForm P) : Represented (Reduced.zero A) := ⟨G.zeroNF A, G.zeroNF_value A⟩

theorem comp {A B C : NormalForm P} {f : Hom A B} {g : Hom B C}
    (hf : Represented f) (hg : Represented g) : Represented (Reduced.comp f g) := by
  obtain ⟨s, hs⟩ := hf
  obtain ⟨t, ht⟩ := hg
  exact ⟨G.cut s t, (cut_single s t).trans (congrArgTwo Reduced.comp hs ht)⟩

theorem tensor (o : Op) {A B C D : NormalForm P} {f : Hom A C} {g : Hom B D}
    (hf : Represented f) (hg : Represented g) : Represented (Reduced.tensor o f g) := by
  obtain ⟨s, hs⟩ := hf
  obtain ⟨t, ht⟩ := hg
  cases o with
  | conj => exact ⟨s.tensorConj t, (G.tensorConj_value s t).trans (congrArgTwo (Reduced.tensor .conj) hs ht)⟩
  | disj => exact ⟨s.tensorDisj t, (G.tensorDisj_value s t).trans (congrArgTwo (Reduced.tensor .disj) hs ht)⟩

theorem fst (A B : NormalForm P) : Represented (Reduced.fst A B) := ⟨G.fstProof A B, G.fstProof_value A B⟩
theorem snd (A B : NormalForm P) : Represented (Reduced.snd A B) := ⟨G.sndProof A B, G.sndProof_value A B⟩
theorem inl (A B : NormalForm P) : Represented (Reduced.inl A B) := ⟨G.inlProof A B, G.inlProof_value A B⟩
theorem inr (A B : NormalForm P) : Represented (Reduced.inr A B) := ⟨G.inrProof A B, G.inrProof_value A B⟩
theorem diag (A : NormalForm P) : Represented (Reduced.diag A) := ⟨G.diagProof A, G.diagProof_value A⟩
theorem codiag (A : NormalForm P) : Represented (Reduced.codiag A) := ⟨G.codiagProof A, G.codiagProof_value A⟩

theorem pair {X A B : NormalForm P} {f : Hom X A} {g : Hom X B}
    (hf : Represented f) (hg : Represented g) : Represented (Reduced.pair f g) :=
  (diag X).comp (hf.tensor .conj hg)

theorem copair {X A B : NormalForm P} {f : Hom A X} {g : Hom B X}
    (hf : Represented f) (hg : Represented g) : Represented (Reduced.copair f g) :=
  (hf.tensor .disj hg).comp (codiag X)

end Represented
end DosenPetric.Reduced.Gentzen
