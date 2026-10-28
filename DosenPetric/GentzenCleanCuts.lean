module

public import DosenPetric.GentzenAtomizedBlockedNormalization
public import DosenPetric.PositiveThinningAtomization

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u} {Γ Δ Θ Λ : List (NormalForm P)} {C : NormalForm P}

/-- Atomize first, then normalize tied contractions while retaining
atomization. Both representatives have the original sequents. -/
theorem clean_cut_premises (f : G P Γ (C::Δ)) (g : G P (C::Θ) Λ)
    (ht : G.Topmost f g) :
    ∃ (f' : G P Γ (C::Δ)) (g' : G P (C::Θ) Λ),
      G.Topmost f' g' ∧ f'.Atomized ∧ g'.Atomized ∧
      ofTerm f'.denote = ofTerm f.denote ∧ ofTerm g'.denote = ofTerm g.denote ∧
      AllBlockedR f' ∧ AllBlockedL g' := by
  have hta : G.Topmost (G.atomize f) (G.atomize g) :=
    ⟨G.atomize_cutFree f ht.1,G.atomize_cutFree g ht.2⟩
  obtain ⟨f',hcf,haF,heF,hbF⟩ := blocked_normalization_right_atomized
    (G.atomize f) (G.atomize g) hta (G.atomize_atomized f)
  obtain ⟨g',hcg,haG,heG,hbG⟩ := blocked_normalization_left_atomized
    f' (G.atomize g) ⟨hcf,hta.2⟩ (G.atomize_atomized g)
  exact ⟨f',g',⟨hcf,hcg⟩,haF,haG,heF.trans (G.atomize_denote f),
    heG.trans (G.atomize_denote g),hbF,hbG⟩

/-- Every topmost cut has equivalent premises that are simultaneously
atomized and blocked at every tied contraction. -/
theorem clean_cut_normalization (f : G P Γ (C::Δ)) (g : G P (C::Θ) Λ)
    (ht : G.Topmost f g) :
    ∃ (f' : G P Γ (C::Δ)) (g' : G P (C::Θ) Λ),
      G.Topmost f' g' ∧ f'.Atomized ∧ g'.Atomized ∧
      ofTerm (G.cut f' g').denote = ofTerm (G.cut f g).denote ∧
      (∀ {U V : List (NormalForm P)} {w : G P U V}
        (a : ProofAddress g' w) (x : At U C),
        g'.TiedRight (a.traceAt .left x) → BlockedL w) ∧
      (∀ {U V : List (NormalForm P)} {w : G P U V}
        (a : ProofAddress f' w) (x : At V C),
        f'.TiedLeft (a.traceAt .right x) → BlockedR w) := by
  obtain ⟨f',g',ht',haF,haG,heF,heG,hbF,hbG⟩ := clean_cut_premises f g ht
  exact ⟨f',g',ht',haF,haG,Rules.cut_congr heF heG,hbG,hbF⟩
end DosenPetric.Reduced.Gentzen
