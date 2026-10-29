module

public import DosenPetric.GentzenDistributiveMono

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.BlockedLeftDisj
universe u
variable {P : Type u}

/-- Exchange the final two factors, retaining the first factor. -/
def terminalCross (Y Q X : NormalForm P) : Hom (.conj (.conj Y Q) X) (.conj (.conj Y X) Q) :=
  pair (pair (comp (fst (.conj Y Q) X) (fst Y Q)) (snd (.conj Y Q) X))
    (comp (fst (.conj Y Q) X) (snd Y Q))

def kernel (S C R : NormalForm P) : Hom (.conj S (.disj C R)) (.disj (.conj C S) R) :=
  splice (id (.disj C R)) (id (.conj C S))

theorem kernel_selected (S C R : NormalForm P) :
    comp (kernel S C R) (tensor .disj (fst C S) (id R)) = snd S (.disj C R) := by
  simp only [kernel,splice,Laws.tensor_id,Laws.comp_id,Laws.id_comp]
  rw [Laws.assoc,Laws.tensor_comp,← Laws.snd_swap,Laws.id_comp,← Laws.dist_snd]

theorem sharedOutput_natural {D E D' E' R : NormalForm P} (f : Hom D D') (g : Hom E E') :
    comp (BlockedMix.sharedOutput D E R) (tensor .disj (tensor .disj f g) (id R)) =
      comp (tensor .disj (tensor .disj f (id R)) (tensor .disj g (id R)))
        (BlockedMix.sharedOutput D' E' R) := by
  simp only [BlockedMix.sharedOutput,BlockedMix.copair_post,BlockedMix.tensor_copair,
    Laws.tensor_comp,Laws.id_comp,Laws.inl_nat,Laws.inr_nat]

/-- The two selected input copies precede their respective terminal formulas. -/
def parent (C F H A B : NormalForm P) :
    Hom (.conj C (.conj (.conj F H) (.disj A B)))
      (.disj (.conj C (.conj F A)) (.conj C (.conj H B))) :=
  comp (assocR .conj C (.conj F H) (.disj A B))
    (comp (tensor .conj
      (pair (tensor .conj (id C) (fst F H)) (tensor .conj (id C) (snd F H))) (id (.disj A B)))
      (comp (ofTerm (Rules.sourceConj (.conj C F) (.conj C H) A B))
        (tensor .disj (assocL .conj C F A) (assocL .conj C H B))))

def input (F H Q X : NormalForm P) :
    Hom (.conj (.conj (.conj F H) Q) X) (.conj (.conj (.conj F X) (.conj H X)) Q) :=
  comp (terminalCross (.conj F H) Q X)
    (tensor .conj
      (BlockedMix.sharedInput (snd F H) (fst F H)) (id Q))

def reconstruction (C F H A B R : NormalForm P) :
    Hom (.conj (.conj (.conj F H) (.disj A B)) (.disj C R))
      (.disj (.disj (.conj C (.conj F A)) (.conj C (.conj H B))) R) :=
  comp (input F H (.disj A B) (.disj C R))
    (comp (ofTerm (Rules.sourceConj (.conj F (.disj C R)) (.conj H (.disj C R)) A B))
      (comp (tensor .disj
        (comp (terminalCross F (.disj C R) A) (kernel (.conj F A) C R))
        (comp (terminalCross H (.disj C R) B) (kernel (.conj H B) C R)))
        (BlockedMix.sharedOutput (.conj C (.conj F A)) (.conj C (.conj H B)) R)))

end DosenPetric.Reduced.Gentzen.BlockedLeftDisj
