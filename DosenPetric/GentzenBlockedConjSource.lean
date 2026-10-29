module

public import DosenPetric.GentzenBlockedConjNative
public import DosenPetric.GentzenBlockedMixSource

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.BlockedConj
universe u
variable {P : Type u}

/-- The original common input route factors through both selected child heads. -/
theorem source_denote {K Γ Θ Δ Λ : List (NormalForm P)} {A B C : NormalForm P}
    (r : Route K (Γ++Θ)) (x : At K C) (a : At Γ C) (b : At Θ C)
    (p : Route x.erase a.erase) (q : Route x.erase b.erase)
    (ha : r.firstBlock.get a = x) (hb : r.secondBlock.get b = x)
    (hp : ∀ {B : NormalForm P} (v : At a.erase B),
      r.firstBlock.get (a.retain v) = x.retain (p.get v))
    (hq : ∀ {B : NormalForm P} (v : At b.erase B),
      r.secondBlock.get (b.retain v) = x.retain (q.get v))
    (f : G P Γ (A::Δ)) (g : G P Θ (B::Λ)) :
    comp (x.toHead.arrow .conj) (comp (r.sideArrow .conj) (ofTerm (G.conjR f g).denote)) =
      ofTerm (headParent p q (a.toHead.left f) (b.toHead.left g)).denote := by
  have hs : comp (r.sideArrow .conj) (ofTerm (append .conj Γ Θ).invTerm) =
      pair (r.firstBlock.sideArrow .conj) (r.secondBlock.sideArrow .conj) := by
    have he := Route.append_split .conj r.firstBlock r.secondBlock
    rw [Route.blocks_append] at he
    exact he
  have hp' := Route.selected_factor .conj r.firstBlock x a p ha hp
  have hq' := Route.selected_factor .conj r.secondBlock x b q hb hq
  dsimp only [side,sideM,category] at hp' hq'
  rw [headParent_denote,ExchangeScript.left_denote,ExchangeScript.left_denote]
  change comp (x.toHead.arrow .conj) (comp (r.sideArrow .conj)
    (ofTerm (Rules.conjRight f.denote g.denote))) = _
  simp only [Rules.conjRight,ofTerm_comp,ofTerm_tensor,ofTerm_id]
  rw [← Laws.assoc (r.sideArrow .conj),hs]
  rw [← Laws.assoc (x.toHead.arrow .conj),ProductCalculation.pair_pre,hp',hq',← BlockedMix.pair_tensor]
  simp only [Laws.assoc]
  rw [← Laws.assoc (tensor .conj (a.toHead.arrow .conj) (b.toHead.arrow .conj)),Laws.tensor_comp]
  unfold sharedParent
  rw [← BlockedMix.pair_tensor]
  simp only [Laws.assoc]
  rfl

end DosenPetric.Reduced.Gentzen.BlockedConj
