module

public import DosenPetric.GentzenBlockedRightMixNative
public import DosenPetric.GentzenBlockedMixSource

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.BlockedMix
universe u
variable {P : Type u}

theorem tensor_copair {A B D E X : NormalForm P}
    (f : Hom A D) (g : Hom B E) (h : Hom D X) (k : Hom E X) :
    comp (tensor .disj f g) (copair h k) = copair (comp f h) (comp g k) := by
  apply Reduced.disj_ext
  · have he : comp (inl D E) (copair h k) = h := (disjDiagonal P).pair_fst h k
    have hh : comp (inl A B) (copair (comp f h) (comp g k)) = comp f h :=
      (disjDiagonal P).pair_fst (comp f h) (comp g k)
    rw [hh,← Laws.assoc,Laws.inl_nat,Laws.assoc,he]
  · have he : comp (inr D E) (copair h k) = k := (disjDiagonal P).pair_snd h k
    have hh : comp (inr A B) (copair (comp f h) (comp g k)) = comp g k :=
      (disjDiagonal P).pair_snd (comp f h) (comp g k)
    rw [hh,← Laws.assoc,Laws.inr_nat,Laws.assoc,he]

/-- Factor the common output route at the two exact original child positions. -/
theorem right_source_denote {K Γ Θ Δ Λ : List (NormalForm P)} {C : NormalForm P}
    (r : Route K (Λ++Δ)) (x : At K C) (a : At Δ C) (b : At Λ C)
    (p : Route x.erase a.erase) (q : Route x.erase b.erase)
    (ha : r.secondBlock.get a = x) (hb : r.firstBlock.get b = x)
    (hp : ∀ {B : NormalForm P} (v : At a.erase B),
      r.secondBlock.get (a.retain v) = x.retain (p.get v))
    (hq : ∀ {B : NormalForm P} (v : At b.erase B),
      r.firstBlock.get (b.retain v) = x.retain (q.get v))
    (f : G P Γ Δ) (g : G P Θ Λ) :
    comp (ofTerm (G.mix f g).denote) (comp (r.sideArrow .disj) (x.toHead.arrow .disj)) =
      ofTerm (rightHeadParent p q (a.toHead.right f) (b.toHead.right g)).denote := by
  have hs := Route.append_split .disj r.firstBlock r.secondBlock
  rw [Route.blocks_append] at hs
  dsimp only [side,sideD,sideM,disjMonoidal,opposite,category,split,disjDiagonal,DiagonalData.pair] at hs
  change comp (ofTerm (append .disj Λ Δ).toTerm) (r.sideArrow .disj) =
    copair (r.firstBlock.sideArrow .disj) (r.secondBlock.sideArrow .disj) at hs
  have hp' := Route.selected_factor .disj r.secondBlock x a p ha hp
  have hq' := Route.selected_factor .disj r.firstBlock x b q hb hq
  dsimp only [side,sideM,disjMonoidal,opposite,category] at hp' hq'
  rw [rightHeadParent_denote,ExchangeScript.right_denote,ExchangeScript.right_denote]
  change comp (ofTerm (Rules.mix f.denote g.denote)) _ = _
  simp only [Rules.mix,ofTerm_comp,ofTerm_tensor,mix_term,Laws.assoc]
  rw [← Laws.assoc (ofTerm (append .disj Λ Δ).toTerm),hs,copair_post,hq',hp',← tensor_copair]
  rw [← Laws.assoc (mix (succ Λ) (succ Δ)),Laws.mix_nat]
  simp only [Laws.assoc]
  rw [← Laws.assoc (tensor .conj (ofTerm g.denote) (ofTerm f.denote)),Laws.tensor_comp]
  rfl

end DosenPetric.Reduced.Gentzen.BlockedMix
