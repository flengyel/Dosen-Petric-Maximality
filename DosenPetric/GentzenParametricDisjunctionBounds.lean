module

public import DosenPetric.GentzenParametricDisjunction
public import DosenPetric.GentzenDisjunctionSuccedentBounds

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.W5.ParametricDisjunction
universe u
variable {P : Type u} {A B C : NormalForm P} {F K U L Δ Λ : List (NormalForm P)}
variable (p : ContractionSelection C F K) (q : ContractionSelection C U L)
variable (f : G P (A::F) Δ) (g : G P (B::U) Λ)

theorem old_rank : (old p q f g).rho .left (.there (p.chain q).keep)=
    1+(p.selected.map (fun a => f.rho .left (.there a))).sum+
      (q.selected.map (fun a => g.rho .left (.there a))).sum+p.arity+q.arity := by
  have hn : 2≤(ContractionSelection.fixed (.disj A B) (p.chain q)).arity := by
    change 2≤(p.chain q).arity
    rw [ContractionSelection.chain_count]
    have hp:=p.arity_pos; have hq:=q.arity_pos; omega
  let R : At (.disj A B::(p.erased++L)) C→Nat := fun a => (old p q f g).rho .left a
  let r : At (.disj A B::(F++U)) C→Nat := fun a => (G.disjL f g).rho .left a
  have h:=(ContractionSelection.fixed (.disj A B) (p.chain q)).performL_rank (Δ++Λ) (G.disjL f g)
  change R (.there (p.chain q).keep)=
    ((p.chain q).selected.map At.there |>.map r).sum+(if 2≤(ContractionSelection.fixed (.disj A B) (p.chain q)).arity then 1 else 0) at h
  rw [ite_eq_left hn,ContractionSelection.chain_selected] at h
  simp only [List.map_map,List.map_append,List.sum_append,Function.comp_def] at h
  change (old p q f g).rho .left (.there (p.chain q).keep)=
    (p.selected.map (fun a => (G.disjL f g).rho .left (.there (a.before U)))).sum+
      (q.selected.map (fun a => (G.disjL f g).rho .left (.there (At.shift F a)))).sum+1 at h
  simp only [G.rho_disjL_f,G.rho_disjL_g] at h
  rw [G.sum_map_one_add,G.sum_map_one_add,p.selected_length,q.selected_length] at h
  omega


def limit : Nat := (old p q f g).rho .left (.there (p.chain q).keep)

theorem innerF_lt : (innerF p f).rho .left (.there p.keep)<limit p q f g := by
  change ((p.prependFixed [A]).performL _ f).rho .left (.there p.keep)<(old p q f g).rho .left (.there (p.chain q).keep)
  rw [W6.NativeLeft.premise_rank,old_rank]
  have hp:=p.overhead_bound; have hq:=q.arity_pos; omega

theorem innerG_lt : (innerG q g).rho .left (.there q.keep)<limit p q f g := by
  change ((q.prependFixed [B]).performL _ g).rho .left (.there q.keep)<(old p q f g).rho .left (.there (p.chain q).keep)
  rw [W6.NativeLeft.premise_rank,old_rank]
  have hp:=p.arity_pos; have hq:=q.overhead_bound; omega

theorem innerF_bound : ContractionBound .left C (limit p q f g) (innerF p f)
    (fun x => x.index=p.keep.index+1) := by
  apply ContractionBound.bounded
  intro x hx
  change At (A::K) C at x
  have he : x=.there p.keep := At.index_injective _ _ hx
  subst x; exact innerF_lt p q f g

theorem innerG_bound : ContractionBound .left C (limit p q f g) (innerG q g)
    (fun x => x.index=q.keep.index+1) := by
  apply ContractionBound.bounded
  intro x hx
  change At (B::L) C at x
  have he : x=.there q.keep := At.index_injective _ _ hx
  subst x; exact innerG_lt p q f g

theorem body_bound : ContractionBound .left C (limit p q f g) (body p q f g)
    (fun x => x.index=(p.chain q).keep.index) := by
  unfold body
  apply (block p q).left_bound (block_bound p q) _ _ (fun i=>i=(p.chain q).keep.index) (body_blocked p q f g)
  apply BlockedSource.native_source_bound _ _
    (fun i=>copyIndex (block p q).gs i=(p.chain q).keep.index)
  · apply (innerF_bound p q f g).mono
    intro x hx
    change At (A::K) C at x
    change 0<x.index ∧ copyIndex (p.mergeBlock q).gs (exchangeIndex 0 1 (K++L).length x.index)=(p.chain q).keep.index at hx
    have hx0 : 0<x.index := hx.1
    have hi:=x.index_lt
    simp only [List.length_cons] at hi
    rw [EntryFrame.exchange_head_index _ x.index hx.1 (by simp only [List.length_append]; omega)] at hx
    have hm:=(DisjunctionSuccedent.merge_selected_index p q _).mp hx.2
    have he:=DisjunctionSuccedent.before_index (x.index-1) K.length (gaps p.gs).length (gaps q.gs).length (by omega) hm
    change x.index=p.keep.index+1
    rw [p.keep_index]; omega
  · apply (innerG_bound p q f g).mono
    intro x hx
    change At (B::L) C at x
    change 0<x.index ∧ copyIndex (p.mergeBlock q).gs (exchangeIndex 0 1 (K++L).length (K.length+x.index))=(p.chain q).keep.index at hx
    have hx0 : 0<x.index := hx.1
    have hi:=x.index_lt
    simp only [List.length_cons] at hi
    rw [EntryFrame.exchange_head_index _ (K.length+x.index) (by omega) (by simp only [List.length_append]; omega)] at hx
    have hm:=(DisjunctionSuccedent.merge_selected_index p q _).mp hx.2
    have hk : (gaps p.gs).length<K.length := by have h:=p.keep.index_lt; rwa [p.keep_index] at h
    have he : x.index=q.keep.index+1 := by rw [q.keep_index]; omega
    exact he

theorem rotate_index (k i n : Nat) (hk : k<n) (h : exchangeIndex 0 n 1 i=k+1) : i=k := by
  have he : exchangeIndex 0 n 1 k=k+1 := by
    unfold exchangeIndex
    simp only [Nat.zero_add]
    rw [ite_eq_right (by omega),ite_eq_left hk]
  have hi:=congrArg (exchangeIndex 0 1 n) (h.trans he.symm)
  simpa only [exchangeIndex_inverse] using hi

theorem repair_bound : ContractionBound .left C (limit p q f g) (repair p q f g)
    (fun x => x.index=(.there (p.chain q).keep : At (.disj A B::(p.erased++L)) C).index) := by
  unfold repair BlockedSource.headL
  apply UnaryCast.exchangeL_bound [] (p.erased++L) [.disj A B] [] _ _ _ _
    (fun i=>i=(p.chain q).keep.index+1)
  apply (body_bound p q f g).mono
  intro x hx
  change exchangeIndex 0 (p.erased++L).length 1 x.index=(p.chain q).keep.index+1 at hx
  exact rotate_index _ _ _ (p.chain q).keep.index_lt hx

theorem reduces {Φ Ξ Ω Ψ : List (NormalForm P)}
    (cutLeft : G P Φ (C::Ξ)) (root : G P (C::Ω) Ψ) :
    ReducesL cutLeft root (old p q f g) (.there (p.chain q).keep) := by
  intro a hr
  refine ⟨repair p q f g,?_,denote p q f g,?_⟩
  · have hc:=hr.cutFree
    change (old p q f g).cutCount=0 at hc
    rw [old_count] at hc
    change (repair p q f g).cutCount=0
    rw [repair_count]; exact hc
  · intro I J v b y hv
    obtain ⟨z,hz,ha⟩:=(a.replacement_cluster_iff (repair p q f g) b .left (.here C Ω) y).mp hv.2.1.1
    have hx : z=.there (p.chain q).keep := hr.entry_unique z ha
    cases hx
    exact (repair_bound p q f g).bound b (.there (p.chain q).keep) rfl y hz hv.2.1.2 hv.2.2.1
end DosenPetric.Reduced.Gentzen.W5.ParametricDisjunction
