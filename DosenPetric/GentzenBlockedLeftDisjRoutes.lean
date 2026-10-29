module

public import DosenPetric.GentzenBlockedLeftDisjCanonical

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.BlockedLeftDisj
universe u
variable {P : Type u}

def sharedParent {C Y F H A B D E : NormalForm P} (p : Hom Y F) (q : Hom Y H)
    (f : Hom (.conj C (.conj F A)) D) (g : Hom (.conj C (.conj H B)) E) :
    Hom (.conj C (.conj Y (.disj A B))) (.disj D E) :=
  comp (tensor .conj (id C) (tensor .conj (pair p q) (id (.disj A B))))
    (comp (parent C F H A B) (tensor .disj f g))

def sharedInput {Y F H X : NormalForm P} (p : Hom Y F) (q : Hom Y H) (Q : NormalForm P) :
    Hom (.conj (.conj Y Q) X) (.conj (.conj (.conj F X) (.conj H X)) Q) :=
  comp (terminalCross Y Q X) (tensor .conj (BlockedMix.sharedInput q p) (id Q))

theorem sharedParent_fan {C Y F H A B D E : NormalForm P} (p : Hom Y F) (q : Hom Y H)
    (f : Hom (.conj C (.conj F A)) D) (g : Hom (.conj C (.conj H B)) E) :
    sharedParent p q f g =
      comp (assocR .conj C Y (.disj A B))
        (comp (tensor .conj (pair (tensor .conj (id C) p) (tensor .conj (id C) q)) (id (.disj A B)))
          (comp (ofTerm (Rules.sourceConj (.conj C F) (.conj C H) A B))
            (tensor .disj (comp (assocL .conj C F A) f) (comp (assocL .conj C H B) g)))) := by
  have hn : comp (tensor .conj (id C) (tensor .conj (pair p q) (id (.disj A B))))
      (assocR .conj C (.conj F H) (.disj A B)) =
      comp (assocR .conj C Y (.disj A B))
        (tensor .conj (tensor .conj (id C) (pair p q)) (id (.disj A B))) :=
    (Laws.assocR_nat .conj (id C) (pair p q) (id (.disj A B))).symm
  have hf : comp (tensor .conj (id C) (pair p q))
      (pair (tensor .conj (id C) (fst F H)) (tensor .conj (id C) (snd F H))) =
      pair (tensor .conj (id C) p) (tensor .conj (id C) q) := by
    rw [ProductCalculation.pair_pre]
    simp only [Laws.tensor_comp,ProductCalculation.pair_fst,ProductCalculation.pair_snd,Laws.id_comp]
  unfold sharedParent parent
  simp only [Laws.assoc]
  rw [← Laws.assoc (tensor .conj (id C) (tensor .conj (pair p q) (id (.disj A B)))),hn]
  simp only [Laws.assoc]
  rw [← Laws.assoc (tensor .conj (tensor .conj (id C) (pair p q)) (id (.disj A B))),
    Laws.tensor_comp,hf,Laws.id_comp,Laws.tensor_comp]

theorem input_routes {Y F H X : NormalForm P} (p : Hom Y F) (q : Hom Y H) (Q : NormalForm P) :
    comp (tensor .conj (tensor .conj (pair p q) (id Q)) (id X)) (input F H Q X) =
      sharedInput p q Q := by
  simp only [sharedInput,input,terminalCross,BlockedMix.sharedInput,
    ProductCalculation.tensor_pair,ProductCalculation.pair_pre,
    ProductCalculation.pair_fst,ProductCalculation.pair_snd,
    ProductCalculation.pair_fst_comp,Laws.comp_id,Laws.assoc]

/-- The two residual routes may select arbitrary fixed tags, including tags with
    the same formula as one of the distinguished positions. -/
theorem shared_equation {C Y F H A B D E X R : NormalForm P} (p : Hom Y F) (q : Hom Y H)
    (f : Hom (.conj C (.conj F A)) D) (g : Hom (.conj C (.conj H B)) E)
    (h : Hom X (.disj C R)) :
    splice h (sharedParent p q f g) =
      comp (sharedInput p q (.disj A B))
        (comp (ofTerm (Rules.sourceConj (.conj F X) (.conj H X) A B))
          (comp (tensor .disj
            (comp (terminalCross F X A) (splice h f))
            (comp (terminalCross H X B) (splice h g))) (BlockedMix.sharedOutput D E R))) := by
  rw [sharedParent,Splice.context,canonical_equation]
  simp only [← Laws.assoc]
  have he := congrArg (fun v => comp v
    (comp (ofTerm (Rules.sourceConj (.conj F X) (.conj H X) A B))
      (comp (tensor .disj
        (comp (terminalCross F X A) (splice h f))
        (comp (terminalCross H X B) (splice h g))) (BlockedMix.sharedOutput D E R))))
    (input_routes p q (.disj A B))
  simpa only [← Laws.assoc] using he

end DosenPetric.Reduced.Gentzen.BlockedLeftDisj
