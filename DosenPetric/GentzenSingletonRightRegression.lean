module

public import DosenPetric.GentzenRightLogicalRegression

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.SingletonRightRegression

abbrev C : NormalForm Empty := .disj .bot .bot
abbrev premise : G Empty [.bot] [C,.bot,.bot] := BlockedExamples.r _
abbrev other : G Empty [C] [.top] := BlockedExamples.l _
abbrev logical : G Empty [.bot] [C,C] := G.disjR [.bot] [C] [] .bot .bot premise
abbrev old : G Empty [.bot] [C] :=
  G.contractR [.bot] C [[],[]] [] (Nat.le_refl 2) logical

theorem premise_cutFree : premise.CutFree := G.atomize_cutFree _ rfl
theorem other_cutFree : other.CutFree := G.atomize_cutFree _ rfl
theorem old_cutFree : old.CutFree := by
  change premise.cutCount=0
  exact premise_cutFree
theorem contracted_prefix : old.contractedDisjRightPrefix = some 1 := rfl
theorem old_unblocked : ¬ BlockedR old := by
  intro hb
  have h:=hb.disjRightPrefix
  rw [contracted_prefix] at h
  have hn : some 1 ∉ ([none,some 0] : List (Option Nat)) := by decide
  exact hn h

theorem old_reducible : ReducibleR old other ProofAddress.root (.here C []) := by
  refine ⟨⟨old_cutFree,other_cutFree⟩,?_,old_unblocked,?_⟩
  · exact ⟨((ProofAddress.root : ProofAddress old old).cluster_iff_ascend .right _ _).mpr rfl,
      G.LowerContraction.right ..⟩
  · intro I J v b y _ hba
    have h:=ProofAddress.proper_length hba
    change b.path.length < 0 at h
    omega

theorem old_rank : old.rho .right (.here C []) =
    premise.rho .right (.here C [.bot,.bot])+3 := by
  have hc:=G.contractionRankR_eq [.bot] C [[],[]] [] (Nat.le_refl 2) logical
  have hp:=G.rho_disjR_principal [.bot] [C] [] .bot .bot premise
  have hs:=G.rho_disjR_surviving [.bot] [C] [] .bot .bot premise
    (.here C [.bot,.bot]) (.here C [C]) (by rfl)
  change old.rho .right (.here C []) = 1+(logical.rho .right (.here C [C])+
    (logical.rho .right (.there (.here C []))+0)) at hc
  change logical.rho .right (.there (.here C [])) = 1 at hp
  change logical.rho .right (.here C [C]) = 1+premise.rho .right (.here C [.bot,.bot]) at hs
  omega

end DosenPetric.Reduced.Gentzen.SingletonRightRegression
