module

public import DosenPetric.GentzenBlockedDisjEquation
public import DosenPetric.GentzenBlockedRightMixSource

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.BlockedDisj
universe u
variable {P : Type u}

/-- The common output route factors at the two original child tags, including
    equal formula labels at different positions. -/
theorem source_denote {K F U Δ Λ : List (NormalForm P)} {A B C : NormalForm P}
    (r : Route K (Δ++Λ)) (x : At K C) (a : At Δ C) (b : At Λ C)
    (p : Route x.erase a.erase) (q : Route x.erase b.erase)
    (ha : r.firstBlock.get a = x) (hb : r.secondBlock.get b = x)
    (hp : ∀ {D : NormalForm P} (v : At a.erase D),
      r.firstBlock.get (a.retain v) = x.retain (p.get v))
    (hq : ∀ {D : NormalForm P} (v : At b.erase D),
      r.secondBlock.get (b.retain v) = x.retain (q.get v))
    (f : G P (F++[A]) Δ) (g : G P (U++[B]) Λ) :
    comp (ofTerm (BlockedSource.disjLLast f g).denote)
      (comp (r.sideArrow .disj) (x.toHead.arrow .disj)) =
      ofTerm (headParent p q (a.toHead.right f) (b.toHead.right g)).denote := by
  have hs := Route.append_split .disj r.firstBlock r.secondBlock
  rw [Route.blocks_append] at hs
  dsimp only [side,sideD,sideM,disjMonoidal,opposite,category,split,disjDiagonal,DiagonalData.pair] at hs
  change comp (ofTerm (append .disj Δ Λ).toTerm) (r.sideArrow .disj) =
    copair (r.firstBlock.sideArrow .disj) (r.secondBlock.sideArrow .disj) at hs
  have hp' := Route.selected_factor .disj r.firstBlock x a p ha hp
  have hq' := Route.selected_factor .disj r.secondBlock x b q hb hq
  dsimp only [side,sideM,disjMonoidal,opposite,category] at hp' hq'
  rw [headParent_denote,ExchangeScript.right_denote,ExchangeScript.right_denote,
    TerminalFold.disjLLast_denote]
  simp only [Laws.assoc]
  rw [← Laws.assoc (ofTerm (append .disj Δ Λ).toTerm),hs,BlockedMix.copair_post,hp',hq',
    ← BlockedMix.tensor_copair]
  unfold headRightParent
  rw [← Laws.assoc (tensor .disj
      (comp (TerminalFold.into F A) (ofTerm f.denote))
      (comp (TerminalFold.into U B) (ofTerm g.denote))),Laws.tensor_comp]
  simp only [Laws.assoc]

end DosenPetric.Reduced.Gentzen.BlockedDisj
