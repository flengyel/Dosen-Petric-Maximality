module

public import DosenPetric.GentzenConjunctionAntecedentRules

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.W5.ConjunctionAntecedent
universe u
variable {P : Type u} {A B C : NormalForm P} {F K U L Δ Λ : List (NormalForm P)}
variable (p : ContractionSelection C F K) (q : ContractionSelection C U L)
variable (f : G P F (A::Δ)) (g : G P U (B::Λ))

theorem old_rank : (old p q f g).rho .left (p.chain q).keep=
    1+(p.selected.map (fun a => f.rho .left a)).sum+
      (q.selected.map (fun a => g.rho .left a)).sum+p.arity+q.arity := by
  have hn : 2≤(p.chain q).arity := by
    rw [ContractionSelection.chain_count]
    have hp:=p.arity_pos; have hq:=q.arity_pos; omega
  let R : At (p.erased++L) C→Nat := fun a => (old p q f g).rho .left a
  let r : At (F++U) C→Nat := fun a => (G.conjR f g).rho .left a
  have h:=(p.chain q).performL_rank _ (G.conjR f g)
  change R (p.chain q).keep=((p.chain q).selected.map r).sum+(if 2≤(p.chain q).arity then 1 else 0) at h
  rw [ContractionSelection.chain_selected,ite_eq_left hn] at h
  simp only [List.map_append,List.sum_append,List.map_map,Function.comp_def] at h
  change (old p q f g).rho .left (p.chain q).keep=
    (p.selected.map (fun a => (G.conjR f g).rho .left (a.before U))).sum+
      (q.selected.map (fun a => (G.conjR f g).rho .left (At.shift F a))).sum+1 at h
  simp only [G.rho_conjR_f_left,G.rho_conjR_g_left] at h
  let rf : At F C→Nat := fun a => f.rho .left a
  let rg : At U C→Nat := fun a => g.rho .left a
  change R (p.chain q).keep=(p.selected.map (fun a => 1+rf a)).sum+
    (q.selected.map (fun a => 1+rg a)).sum+1 at h
  rw [G.sum_map_one_add,G.sum_map_one_add,p.selected_length,q.selected_length] at h
  change R (p.chain q).keep=1+(p.selected.map rf).sum+(q.selected.map rg).sum+p.arity+q.arity
  omega

theorem repair_rank : (repair p q f g).rho .left (p.chain q).keep=
    3+(p.performL _ f).rho .left p.keep+(q.performL _ g).rho .left q.keep := by
  have hk:=(p.mergeBlock q).rankL_keep (Nat.le_refl 2) _ (middle p q f g)
  have hs:=(p.mergeBlock q).rankL_sum (Nat.le_refl 2) _ (middle p q f g)
  rw [p.merge_retained q] at hk
  let r : At (K++L) C→Nat := fun a => (middle p q f g).rho .left a
  change (p.mergeBlock q).rankL (Nat.le_refl 2) _ (middle p q f g)=1+((p.mergeBlock q).selected.map r).sum at hs
  rw [p.merge_selected q] at hs
  change (p.mergeBlock q).rankL (Nat.le_refl 2) _ (middle p q f g)=1+(r (p.keep.before L)+(r (At.shift K q.keep)+0)) at hs
  simp only [r,middle,G.rho_conjR_f_left,G.rho_conjR_g_left] at hs
  change (p.mergeBlock q).rankL (Nat.le_refl 2) _ (middle p q f g)=_ at hs
  change (repair p q f g).rho .left (p.chain q).keep=_ at hk
  omega

theorem endpoint_le : (repair p q f g).rho .left (p.chain q).keep≤(old p q f g).rho .left (p.chain q).keep := by
  rw [repair_rank,old_rank,p.performL_rank,q.performL_rank]
  have hp:=p.overhead_bound; have hq:=q.overhead_bound
  omega

theorem reduces {Φ Ξ Ω Ψ : List (NormalForm P)}
    (cutLeft : G P Φ (C::Ξ)) (root : G P (C::Ω) Ψ) :
    ReducesL cutLeft root (old p q f g) (p.chain q).keep := by
  intro a hr
  refine ⟨repair p q f g,?_,denote p q f g,?_⟩
  · have hc:=hr.cutFree
    change (old p q f g).cutCount=0 at hc
    rw [old_count] at hc
    change (repair p q f g).cutCount=0
    rw [repair_count]
    exact hc
  · intro I J v b y hv
    exact ReducibilityBoundary.descendants_left a (p.chain q).keep _ (blocked p q f g)
      (fun z hz => hr.entry_unique z hz) (endpoint_le p q f g) b y hv

end DosenPetric.Reduced.Gentzen.W5.ConjunctionAntecedent
