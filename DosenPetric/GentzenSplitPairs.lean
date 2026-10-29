module

public import DosenPetric.GentzenDistributiveMono

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

/-- A pair of arrows with a chosen retraction of their pairing. -/
structure SplitPair (A B C : NormalForm P) where
  first : Hom A B
  second : Hom A C
  retraction : Hom (.conj B C) A
  recover : comp (pair first second) retraction = id A

namespace SplitPair
variable {A B C : NormalForm P}

def product (A B : NormalForm P) : SplitPair (.conj A B) A B where
  first := fst A B
  second := snd A B
  retraction := id (.conj A B)
  recover := by
    rw [Laws.comp_id]
    have he := (conjDiagonal P).pair_eta (id (.conj A B))
    change pair (comp (id (.conj A B)) (fst A B))
      (comp (id (.conj A B)) (snd A B)) = id (.conj A B) at he
    simpa only [Laws.id_comp] using he

def sumLeft (s : SplitPair A B C) (R : NormalForm P) :
    SplitPair (.disj A R) (.disj B R) (.disj C R) where
  first := tensor .disj s.first (id R)
  second := tensor .disj s.second (id R)
  retraction := comp (DistributiveMono.retraction B C R) (tensor .disj s.retraction (id R))
  recover := by
    have he : pair (tensor .disj s.first (id R)) (tensor .disj s.second (id R)) =
        comp (tensor .disj (pair s.first s.second) (id R)) (DistributiveMono.comparison B C R) := by
      rw [DistributiveMono.comparison,ProductCalculation.pair_pre]
      simp only [Laws.tensor_comp,ProductCalculation.pair_fst,ProductCalculation.pair_snd,Laws.id_comp]
    rw [he,Laws.assoc,← Laws.assoc (DistributiveMono.comparison B C R),
      DistributiveMono.comparison_retraction,Laws.id_comp,Laws.tensor_comp,
      s.recover,Laws.id_comp,Laws.tensor_id]

def sumRight (L : NormalForm P) (s : SplitPair A B C) :
    SplitPair (.disj L A) (.disj L B) (.disj L C) where
  first := tensor .disj (id L) s.first
  second := tensor .disj (id L) s.second
  retraction := comp (tensor .conj (swap .disj L B) (swap .disj L C))
    (comp (s.sumLeft L).retraction (swap .disj A L))
  recover := by
    have hn {D : NormalForm P} (v : Hom A D) :
        comp (swap .disj L A) (comp (tensor .disj v (id L)) (swap .disj D L)) =
          tensor .disj (id L) v := by
      rw [← Laws.assoc,Laws.swap_nat,Laws.assoc,Laws.swap_swap,Laws.comp_id]
    have he : pair (tensor .disj (id L) s.first) (tensor .disj (id L) s.second) =
        comp (swap .disj L A)
          (comp (pair (s.sumLeft L).first (s.sumLeft L).second)
            (tensor .conj (swap .disj B L) (swap .disj C L))) := by
      rw [BlockedMix.pair_tensor,ProductCalculation.pair_pre]
      change _ = pair (comp (swap .disj L A) (comp (tensor .disj s.first (id L)) (swap .disj B L)))
        (comp (swap .disj L A) (comp (tensor .disj s.second (id L)) (swap .disj C L)))
      rw [hn,hn]
    rw [he]
    simp only [Laws.assoc]
    rw [← Laws.assoc (tensor .conj (swap .disj B L) (swap .disj C L)),
      Laws.tensor_comp,Laws.swap_swap,Laws.swap_swap,Laws.tensor_id,Laws.id_comp]
    rw [← Laws.assoc (pair (s.sumLeft L).first (s.sumLeft L).second),
      (s.sumLeft L).recover,Laws.id_comp,Laws.swap_swap]

theorem ext (s : SplitPair A B C) {S : NormalForm P} (f g : Hom S A)
    (h₁ : comp f s.first = comp g s.first)
    (h₂ : comp f s.second = comp g s.second) : f = g := by
  apply cancel_right f g (pair s.first s.second) s.retraction s.recover
  rw [ProductCalculation.pair_pre,ProductCalculation.pair_pre,h₁,h₂]

end SplitPair
end DosenPetric.Reduced.Gentzen
