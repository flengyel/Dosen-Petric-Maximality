module

public import DosenPetric.GentzenDisjunctionSuccedentBoth

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.W5.DisjunctionSuccedent
universe u
variable {P : Type u} {A B C : NormalForm P} {F K U L Γ Θ : List (NormalForm P)}
variable (p : ContractionSelection C F K) (q : ContractionSelection C U L)
variable (f : G P (A::Γ) F) (g : G P (B::Θ) U)

theorem old_rank : (old p q f g).rho .right (p.chain q).keep=
    1+(p.selected.map (fun a => f.rho .right a)).sum+
      (q.selected.map (fun a => g.rho .right a)).sum+p.arity+q.arity := by
  have hn : 2≤(p.chain q).arity := by
    rw [ContractionSelection.chain_count]
    have hp:=p.arity_pos; have hq:=q.arity_pos; omega
  let R : At (p.erased++L) C→Nat := fun a => (old p q f g).rho .right a
  let r : At (F++U) C→Nat := fun a => (G.disjL f g).rho .right a
  have h:=(p.chain q).performR_rank _ (G.disjL f g)
  change R (p.chain q).keep=((p.chain q).selected.map r).sum+(if 2≤(p.chain q).arity then 1 else 0) at h
  rw [ContractionSelection.chain_selected,ite_eq_left hn] at h
  simp only [List.map_append,List.sum_append,List.map_map,Function.comp_def] at h
  change (old p q f g).rho .right (p.chain q).keep=
    (p.selected.map (fun a => (G.disjL f g).rho .right (a.before U))).sum+
      (q.selected.map (fun a => (G.disjL f g).rho .right (At.shift F a))).sum+1 at h
  simp only [G.rho_disjL_f_right,G.rho_disjL_g_right] at h
  let rf : At F C→Nat := fun a => f.rho .right a
  let rg : At U C→Nat := fun a => g.rho .right a
  change R (p.chain q).keep=(p.selected.map (fun a => 1+rf a)).sum+
    (q.selected.map (fun a => 1+rg a)).sum+1 at h
  rw [G.sum_map_one_add,G.sum_map_one_add,p.selected_length,q.selected_length] at h
  change R (p.chain q).keep=1+(p.selected.map rf).sum+(q.selected.map rg).sum+p.arity+q.arity
  omega

def limit : Nat := (old p q f g).rho .right (p.chain q).keep

theorem innerF_lt : (innerF p f).rho .right p.keep<limit p q f g := by
  change (p.performR _ f).rho .right p.keep<(old p q f g).rho .right (p.chain q).keep
  rw [p.performR_rank,old_rank]
  have hp:=p.overhead_bound; have hq:=q.arity_pos
  omega

theorem innerG_lt : (innerG q g).rho .right q.keep<limit p q f g := by
  change (q.performR _ g).rho .right q.keep<(old p q f g).rho .right (p.chain q).keep
  rw [q.performR_rank,old_rank]
  have hp:=p.arity_pos; have hq:=q.overhead_bound
  omega

theorem merge_selected_index (i : Nat) :
    copyIndex (p.mergeBlock q).gs i=(p.chain q).keep.index ↔
      i=(gaps p.gs).length ∨ i=K.length+(gaps q.gs).length := by
  have hk:=(p.mergeBlock q).keep_index.symm.trans (congrArg At.index (p.merge_retained q))
  rw [←hk,copyIndex_selected]
  have hp:=p.lower_length
  change i∈copyOffsets [gaps p.gs,p.tail++gaps q.gs] ↔ _
  simp only [copyOffsets,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false,List.length_append]
  simp only [gaps,List.length_append] at hp ⊢
  omega

theorem before_index (i k x z : Nat) (hi : i<k) (hm : i=x ∨ i=k+z) : i=x := by omega
theorem shift_index (i k x z : Nat) (hx : x<k) (hm : k+i=x ∨ k+i=k+z) : i=z := by omega

theorem innerF_bound : ContractionBound .right C (limit p q f g) (innerF p f) (fun x => x.index=p.keep.index) := by
  apply ContractionBound.bounded
  intro x hx
  change At K C at x
  have he : x=p.keep := At.index_injective _ _ hx
  subst x
  exact innerF_lt p q f g

theorem innerG_bound : ContractionBound .right C (limit p q f g) (innerG q g) (fun x => x.index=q.keep.index) := by
  apply ContractionBound.bounded
  intro x hx
  change At L C at x
  have he : x=q.keep := At.index_injective _ _ hx
  subst x
  exact innerG_lt p q f g

theorem body_bound : ContractionBound .right C (limit p q f g) (body p q f g)
    (fun x => x.index=(p.chain q).keep.index) := by
  unfold body
  apply (p.mergeBlock q).right_bound (Nat.le_refl 2) _ _ (fun i => i=(p.chain q).keep.index) (body_blocked p q f g)
  apply BlockedSource.native_source_right_bound _ _ (fun i => copyIndex (p.mergeBlock q).gs i=(p.chain q).keep.index)
  · apply (innerF_bound p q f g).mono
    intro x hx
    change At K C at x
    change copyIndex (p.mergeBlock q).gs x.index=(p.chain q).keep.index at hx
    have hm:=(merge_selected_index p q _).mp hx
    rw [p.keep_index]
    exact before_index x.index K.length (gaps p.gs).length (gaps q.gs).length x.index_lt hm
  · apply (innerG_bound p q f g).mono
    intro x hx
    change At L C at x
    change copyIndex (p.mergeBlock q).gs (K.length+x.index)=(p.chain q).keep.index at hx
    have hm:=(merge_selected_index p q _).mp hx
    have hp : (gaps p.gs).length<K.length := by
      have h:=p.keep.index_lt
      rwa [p.keep_index] at h
    rw [q.keep_index]
    exact shift_index x.index K.length (gaps p.gs).length (gaps q.gs).length hp hm

theorem repair_bound : ContractionBound .right C (limit p q f g) (repair p q f g)
    (fun x => x.index=(p.chain q).keep.index) := by
  unfold repair
  apply BlockedSource.headL_right_bound (.disj A B) _ (fun i => i=(p.chain q).keep.index)
  exact body_bound p q f g

theorem reduces {Φ Ξ Ω Ψ : List (NormalForm P)}
    (root : G P Φ (C::Ξ)) (cutRight : G P (C::Ω) Ψ) :
    ReducesR root cutRight (old p q f g) (p.chain q).keep := by
  intro a hr
  refine ⟨repair p q f g,?_,denote p q f g,?_⟩
  · have hc:=hr.cutFree
    change (old p q f g).cutCount=0 at hc
    rw [old_count] at hc
    change (repair p q f g).cutCount=0
    rw [repair_count]; exact hc
  · intro I J v b y hv
    obtain ⟨z,hz,ha⟩:=(a.replacement_cluster_iff (repair p q f g) b .right (.here C Ξ) y).mp hv.2.1.1
    have hx : z=(p.chain q).keep := hr.entry_unique z ha
    cases hx
    exact (repair_bound p q f g).bound b (p.chain q).keep rfl y hz hv.2.1.2 hv.2.2.1

end DosenPetric.Reduced.Gentzen.W5.DisjunctionSuccedent
