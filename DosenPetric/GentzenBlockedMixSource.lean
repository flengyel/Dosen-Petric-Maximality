module

public import DosenPetric.GentzenBlockedMixNative
public import DosenPetric.GentzenSelectedRouteFactor

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace Route

/-- Restrict a common route to the first original binary child. -/
def firstBlock {K F U : List (NormalForm P)} (r : Route K (F++U)) : Route K F :=
  (identity F).map (fun a => r.get (a.before U))

/-- Restrict a common route to the second original binary child. -/
def secondBlock {K F U : List (NormalForm P)} (r : Route K (F++U)) : Route K U :=
  (identity U).map (fun a => r.get (At.shift F a))

theorem firstBlock_get {K F U : List (NormalForm P)} (r : Route K (F++U))
    {A : NormalForm P} (a : At F A) : r.firstBlock.get a = r.get (a.before U) := by
  rw [firstBlock,get_map,get_identity]

theorem secondBlock_get {K F U : List (NormalForm P)} (r : Route K (F++U))
    {A : NormalForm P} (a : At U A) : r.secondBlock.get a = r.get (At.shift F a) := by
  rw [secondBlock,get_map,get_identity]

theorem blocks_append {K F U : List (NormalForm P)} (r : Route K (F++U)) :
    r.firstBlock.append r.secondBlock = r := by
  apply Route.ext_get
  intro A a
  cases At.cases_append F U a with
  | inl h => obtain ⟨a,rfl⟩ := h; rw [append_before,firstBlock_get]
  | inr h => obtain ⟨a,rfl⟩ := h; rw [append_shift,secondBlock_get]

end Route
namespace BlockedMix

theorem pair_tensor {X A B D E : NormalForm P}
    (f : Hom X A) (g : Hom X B) (h : Hom A D) (k : Hom B E) :
    comp (pair f g) (tensor .conj h k) = pair (comp f h) (comp g k) := by
  apply Reduced.conj_ext
  · rw [ProductCalculation.pair_fst,Laws.assoc,← Laws.fst_nat,
      ← Laws.assoc,ProductCalculation.pair_fst]
  · rw [ProductCalculation.pair_snd,Laws.assoc,← Laws.snd_nat,
      ← Laws.assoc,ProductCalculation.pair_snd]

/-- Factor the actual common structural route at both exact selected tags. -/
theorem source_denote {K Γ Θ Δ Λ : List (NormalForm P)} {C : NormalForm P}
    (r : Route K (Θ++Γ)) (x : At K C) (a : At Γ C) (b : At Θ C)
    (p : Route x.erase a.erase) (q : Route x.erase b.erase)
    (ha : r.secondBlock.get a = x) (hb : r.firstBlock.get b = x)
    (hp : ∀ {B : NormalForm P} (v : At a.erase B),
      r.secondBlock.get (a.retain v) = x.retain (p.get v))
    (hq : ∀ {B : NormalForm P} (v : At b.erase B),
      r.firstBlock.get (b.retain v) = x.retain (q.get v))
    (f : G P Γ Δ) (g : G P Θ Λ) :
    comp (x.toHead.arrow .conj) (comp (r.sideArrow .conj) (ofTerm (G.mix f g).denote)) =
      ofTerm (headParent p q (a.toHead.left f) (b.toHead.left g)).denote := by
  have hs : comp (r.sideArrow .conj) (ofTerm (append .conj Θ Γ).invTerm) =
      pair (r.firstBlock.sideArrow .conj) (r.secondBlock.sideArrow .conj) := by
    have he := Route.append_split .conj r.firstBlock r.secondBlock
    rw [Route.blocks_append] at he
    exact he
  have hp' := Route.selected_factor .conj r.secondBlock x a p ha hp
  have hq' := Route.selected_factor .conj r.firstBlock x b q hb hq
  dsimp only [side,sideM,category] at hp' hq'
  rw [headParent_denote,ExchangeScript.left_denote,ExchangeScript.left_denote]
  change comp (x.toHead.arrow .conj) (comp (r.sideArrow .conj)
    (ofTerm (Rules.mix f.denote g.denote))) = _
  simp only [Rules.mix,ofTerm_comp,ofTerm_tensor,mix_term]
  rw [← Laws.assoc (r.sideArrow .conj),hs]
  rw [← Laws.assoc (x.toHead.arrow .conj),ProductCalculation.pair_pre,hq',hp',← pair_tensor]
  simp only [Laws.assoc]
  rw [← Laws.assoc (tensor .conj (b.toHead.arrow .conj) (a.toHead.arrow .conj)),Laws.tensor_comp]
  unfold sharedParent
  simp only [Laws.assoc]
  rfl

end BlockedMix
end DosenPetric.Reduced.Gentzen
