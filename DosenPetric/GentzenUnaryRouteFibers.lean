module

public import DosenPetric.GentzenUnaryRouteRanks

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u} {C : NormalForm P}
namespace ContractionSelection
variable {F U K Δ : List (NormalForm P)}

theorem unary_preimageL (q : ContractionSelection C U K) (hn : 2≤q.arity)
    (g : G P U Δ) (f : G P F Δ) (p : Premise g f) (r : Route U F)
    (hb : g.branches=[⟨F,Δ,f,p⟩])
    (hp : ∀ {A : NormalForm P} (a : At F A),p.parent .left a=some (r.get a)) :
    ∃ a : At F C,q.route.get (r.get a)=q.keep := by
  classical
  apply Classical.byContradiction
  intro hnone
  have hleaf (a : At U C) (ha : a∈q.selected) : g.Leaf .left a := by
    apply (g.leaf_iff_no_predecessor .left a).mpr
    intro v hv
    have hj:=G.branches_complete v.branch
    rw [hb,List.mem_singleton] at hj
    cases v with | mk j x=>
      cases hj
      have he : r.get x=a:=Option.some.inj ((hp x).symm.trans hv)
      exact hnone ⟨x,(congrArg q.route.get he).trans ((q.selected_iff a).mp ha)⟩
  obtain ⟨a,b,ha,hb,hl⟩:=q.block.selected_pair (q.blockArity hn)
  rw [←q.selected_eq] at ha hb
  have he:=g.leaf_indices .left a b (hleaf a ha) (hleaf b hb)
  change a.index=b.index at he
  omega

theorem unary_preimageR (q : ContractionSelection C U K) (hn : 2≤q.arity)
    (g : G P Δ U) (f : G P Δ F) (p : Premise g f) (r : Route U F)
    (hb : g.branches=[⟨Δ,F,f,p⟩])
    (hp : ∀ {A : NormalForm P} (a : At F A),p.parent .right a=some (r.get a)) :
    ∃ a : At F C,q.route.get (r.get a)=q.keep := by
  classical
  apply Classical.byContradiction
  intro hnone
  have hleaf (a : At U C) (ha : a∈q.selected) : g.Leaf .right a := by
    apply (g.leaf_iff_no_predecessor .right a).mpr
    intro v hv
    have hj:=G.branches_complete v.branch
    rw [hb,List.mem_singleton] at hj
    cases v with | mk j x=>
      cases hj
      have he : r.get x=a:=Option.some.inj ((hp x).symm.trans hv)
      exact hnone ⟨x,(congrArg q.route.get he).trans ((q.selected_iff a).mp ha)⟩
  obtain ⟨a,b,ha,hb,hl⟩:=q.block.selected_pair (q.blockArity hn)
  rw [←q.selected_eq] at ha hb
  have he:=g.leaf_indices .right a b (hleaf a ha) (hleaf b hb)
  change a.index=b.index at he
  omega
end ContractionSelection
end DosenPetric.Reduced.Gentzen
