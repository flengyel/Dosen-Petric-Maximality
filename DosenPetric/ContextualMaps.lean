module

public import DosenPetric.ReducedContexts
public import DosenPetric.ReducedStructure

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced
universe u
variable {P : Type u}

namespace Context

/-- Source recursion, pp.318–319; the first comp argument is executed first. -/
def gConj : (K : Context P) → (B : NormalForm P) →
    Term P (.conj (K.plug .top) B) (K.plug B)
  | .hole, B => .leftOut .conj B
  | .left .conj C K, B => .comp (.assocL .conj C (K.plug .top) B)
      (.tensor .conj (.id C) (K.gConj B))
  | .right .conj K C, B => .comp (.swap .conj (.conj (K.plug .top) C) B)
      (.comp (.assocR .conj B (K.plug .top) C)
        (.comp (.tensor .conj (.swap .conj B (K.plug .top)) (.id C))
          (.tensor .conj (K.gConj B) (.id C))))
  | .left .disj C K, B => .comp (.distRight C (K.plug .top) B)
      (.tensor .disj (.id C) (K.gConj B))
  | .right .disj K C, B => .comp (.swap .conj (.disj (K.plug .top) C) B)
      (.comp (.dist B (K.plug .top) C)
        (.comp (.tensor .disj (.swap .conj B (K.plug .top)) (.id C))
          (.tensor .disj (K.gConj B) (.id C))))

/-- Source recursion, p.319. The hole case is B → bot ∨ B. -/
def gDisj : (K : Context P) → (B : NormalForm P) →
    Term P (K.plug B) (.disj (K.plug .bot) B)
  | .hole, B => .leftIn .disj B
  | .left .disj C K, B => .comp (.tensor .disj (.id C) (K.gDisj B))
      (.assocR .disj C (K.plug .bot) B)
  | .right .disj K C, B => .comp (.tensor .disj (K.gDisj B) (.id C))
      (.comp (.tensor .disj (.swap .disj (K.plug .bot) B) (.id C))
        (.comp (.assocL .disj B (K.plug .bot) C)
          (.swap .disj B (.disj (K.plug .bot) C))))
  | .left .conj C K, B => .comp (.tensor .conj (.id C) (K.gDisj B))
      (.dist C (K.plug .bot) B)
  | .right .conj K C, B => .comp (.tensor .conj (K.gDisj B) (.id C))
      (.comp (.tensor .conj (.swap .disj (K.plug .bot) B) (.id C))
        (.comp (.distRight B (K.plug .bot) C)
          (.swap .disj B (.conj (K.plug .bot) C))))

end Context

theorem square_comp {A B C D E F : NormalForm P}
    {a : Hom A B} {b : Hom B C} {r : Hom C F} {l : Hom A D}
    {a' : Hom D E} {b' : Hom E F} {m : Hom B E}
    (ha : comp a m = comp l a') (hb : comp b r = comp m b') :
    comp (comp a b) r = comp l (comp a' b') := by
  rw [Laws.assoc, hb, ← Laws.assoc, ha, Laws.assoc]

theorem tensor_square (o : Op) {A B C D A' B' C' D' : NormalForm P}
    {a : Hom A B} {b : Hom C D} {a' : Hom A' B'} {b' : Hom C' D'}
    {l : Hom A A'} {r : Hom B B'} {l' : Hom C C'} {r' : Hom D D'}
    (ha : comp a r = comp l a') (hb : comp b r' = comp l' b') :
    comp (tensor o a b) (tensor o r r') = comp (tensor o l l') (tensor o a' b') := by
  rw [Laws.tensor_comp, Laws.tensor_comp, ha, hb]

theorem id_square {A B : NormalForm P} (f : Hom A B) :
    comp (id A) f = comp f (id B) := by rw [Laws.id_comp, Laws.comp_id]

namespace Context

theorem gConj_nat (K : Context P) {B D : NormalForm P} (f : Hom B D) :
    comp (ofTerm (K.gConj B)) (K.map f) =
      comp (tensor .conj (id (K.plug .top)) f) (ofTerm (K.gConj D)) := by
  induction K with
  | hole => rw [map_hole]; exact Laws.leftOut_nat .conj f
  | left o C K ih =>
    cases o with
    | conj =>
      change comp (comp (assocL .conj C (K.plug .top) B)
        (tensor .conj (id C) (ofTerm (K.gConj B)))) ((Context.left .conj C K).map f) = _
      rw [map_left]
      have hn := Laws.assocL_nat .conj (id C) (id (K.plug .top)) f
      rw [Laws.tensor_id] at hn
      exact square_comp hn
        (tensor_square .conj (id_square (id C)) ih)
    | disj =>
      change comp (comp (distRight C (K.plug .top) B)
        (tensor .disj (id C) (ofTerm (K.gConj B)))) ((Context.left .disj C K).map f) = _
      rw [map_left]
      have hn := Laws.distRight_nat (id C) (id (K.plug .top)) f
      rw [Laws.tensor_id] at hn
      exact square_comp hn
        (tensor_square .disj (id_square (id C)) ih)
  | right o K C ih =>
    cases o with
    | conj =>
      change comp (comp (swap .conj (.conj (K.plug .top) C) B)
        (comp (assocR .conj B (K.plug .top) C)
          (comp (tensor .conj (swap .conj B (K.plug .top)) (id C))
            (tensor .conj (ofTerm (K.gConj B)) (id C)))))
        ((Context.right .conj K C).map f) = _
      rw [map_right]
      have hn := Laws.assocR_nat .conj f (id (K.plug .top)) (id C)
      rw [Laws.tensor_id] at hn
      exact square_comp (Laws.swap_nat .conj (id _) f)
        (square_comp hn
          (square_comp (tensor_square .conj (Laws.swap_nat .conj f (id _)) (id_square (id C)))
            (tensor_square .conj ih (id_square (id C)))))
    | disj =>
      change comp (comp (swap .conj (.disj (K.plug .top) C) B)
        (comp (dist B (K.plug .top) C)
          (comp (tensor .disj (swap .conj B (K.plug .top)) (id C))
            (tensor .disj (ofTerm (K.gConj B)) (id C)))))
        ((Context.right .disj K C).map f) = _
      rw [map_right]
      have hn := Laws.dist_nat f (id (K.plug .top)) (id C)
      rw [Laws.tensor_id] at hn
      exact square_comp (Laws.swap_nat .conj (id _) f)
        (square_comp hn
          (square_comp (tensor_square .disj (Laws.swap_nat .conj f (id _)) (id_square (id C)))
            (tensor_square .disj ih (id_square (id C)))))

theorem gDisj_nat (K : Context P) {B D : NormalForm P} (f : Hom B D) :
    comp (K.map f) (ofTerm (K.gDisj D)) =
      comp (ofTerm (K.gDisj B)) (tensor .disj (id (K.plug .bot)) f) := by
  symm
  induction K with
  | hole => rw [map_hole]; exact Laws.leftIn_nat .disj f
  | left o C K ih =>
    cases o with
    | disj =>
      change comp (comp (tensor .disj (id C) (ofTerm (K.gDisj B)))
        (assocR .disj C (K.plug .bot) B)) _ = _
      rw [map_left]
      have hn := Laws.assocR_nat .disj (id C) (id (K.plug .bot)) f
      rw [Laws.tensor_id] at hn
      exact square_comp (tensor_square .disj (id_square (id C)) ih) hn
    | conj =>
      change comp (comp (tensor .conj (id C) (ofTerm (K.gDisj B)))
        (dist C (K.plug .bot) B)) _ = _
      rw [map_left]
      have hn := Laws.dist_nat (id C) (id (K.plug .bot)) f
      rw [Laws.tensor_id] at hn
      exact square_comp (tensor_square .conj (id_square (id C)) ih) hn
  | right o K C ih =>
    cases o with
    | disj =>
      change comp (comp (tensor .disj (ofTerm (K.gDisj B)) (id C))
        (comp (tensor .disj (swap .disj (K.plug .bot) B) (id C))
          (comp (assocL .disj B (K.plug .bot) C) (swap .disj B (.disj (K.plug .bot) C))))) _ = _
      rw [map_right]
      have hn := Laws.assocL_nat .disj f (id (K.plug .bot)) (id C)
      rw [Laws.tensor_id] at hn
      exact square_comp (tensor_square .disj ih (id_square (id C)))
        (square_comp (tensor_square .disj (Laws.swap_nat .disj (id _) f) (id_square (id C)))
          (square_comp hn (Laws.swap_nat .disj f (id _))))
    | conj =>
      change comp (comp (tensor .conj (ofTerm (K.gDisj B)) (id C))
        (comp (tensor .conj (swap .disj (K.plug .bot) B) (id C))
          (comp (distRight B (K.plug .bot) C) (swap .disj B (.conj (K.plug .bot) C))))) _ = _
      rw [map_right]
      have hn := Laws.distRight_nat f (id (K.plug .bot)) (id C)
      rw [Laws.tensor_id] at hn
      exact square_comp (tensor_square .conj ih (id_square (id C)))
        (square_comp (tensor_square .conj (Laws.swap_nat .disj (id _) f) (id_square (id C)))
          (square_comp hn (Laws.swap_nat .disj f (id _))))

theorem gConj_top (K : Context P) :
    ofTerm (K.gConj .top) = rightOut .conj (K.plug .top) := by
  induction K with
  | hole =>
    exact ((conjDiagonal P).toUnit_unique (leftOut .conj .top)).trans
      ((conjDiagonal P).toUnit_unique (rightOut .conj .top)).symm
  | left o C K ih =>
    cases o with
    | conj =>
      change comp (assocL .conj C (K.plug .top) .top)
        (tensor .conj (id C) (ofTerm (K.gConj .top))) = _
      rw [ih]; exact rightOut_tensor .conj C (K.plug .top)
    | disj =>
      change comp (distRight C (K.plug .top) .top)
        (tensor .disj (id C) (ofTerm (K.gConj .top))) = _
      rw [ih]; exact distRight_top C (K.plug .top)
  | right o K C ih =>
    cases o with
    | conj =>
      change comp (swap .conj (.conj (K.plug .top) C) .top)
        (comp (assocR .conj .top (K.plug .top) C)
          (comp (tensor .conj (swap .conj .top (K.plug .top)) (id C))
            (tensor .conj (ofTerm (K.gConj .top)) (id C)))) = _
      rw [ih]; exact shuffle_unit_out .conj (K.plug .top) C
    | disj =>
      change comp (swap .conj (.disj (K.plug .top) C) .top)
        (comp (dist .top (K.plug .top) C)
          (comp (tensor .disj (swap .conj .top (K.plug .top)) (id C))
            (tensor .disj (ofTerm (K.gConj .top)) (id C)))) = _
      rw [ih]; exact disj_shuffle_dist_top (K.plug .top) C

theorem gDisj_bot (K : Context P) :
    ofTerm (K.gDisj .bot) = rightIn .disj (K.plug .bot) := by
  induction K with
  | hole =>
    exact ((disjDiagonal P).toUnit_unique (leftIn .disj .bot)).trans
      ((disjDiagonal P).toUnit_unique (rightIn .disj .bot)).symm
  | left o C K ih =>
    cases o with
    | disj =>
      change comp (tensor .disj (id C) (ofTerm (K.gDisj .bot)))
        (assocR .disj C (K.plug .bot) .bot) = _
      rw [ih]; exact rightIn_tensor .disj C (K.plug .bot)
    | conj =>
      change comp (tensor .conj (id C) (ofTerm (K.gDisj .bot)))
        (dist C (K.plug .bot) .bot) = _
      rw [ih, dist_bot, ← Laws.assoc, Laws.tensor_comp, Laws.rightIn_Out,
        Laws.id_comp, Laws.tensor_id, Laws.id_comp]
  | right o K C ih =>
    cases o with
    | disj =>
      change comp (tensor .disj (ofTerm (K.gDisj .bot)) (id C))
        (comp (tensor .disj (swap .disj (K.plug .bot) .bot) (id C))
          (comp (assocL .disj .bot (K.plug .bot) C) (swap .disj .bot (.disj (K.plug .bot) C)))) = _
      rw [ih]; exact shuffle_unit_in .disj (K.plug .bot) C
    | conj =>
      change comp (tensor .conj (ofTerm (K.gDisj .bot)) (id C))
        (comp (tensor .conj (swap .disj (K.plug .bot) .bot) (id C))
          (comp (distRight .bot (K.plug .bot) C) (swap .disj .bot (.conj (K.plug .bot) C)))) = _
      rw [ih]; exact conj_shuffle_dist_bot (K.plug .bot) C

/-- (g eta), p.319, in the stronger form for any existing top-domain arrow. -/
theorem gEta {B : NormalForm P} (K : Context P) (h : Hom .top B) :
    K.map h = comp (rightIn .conj (K.plug .top))
      (comp (tensor .conj (id (K.plug .top)) h)
        (comp (tensor .conj (id (K.plug .top)) (zero B)) (ofTerm (K.gConj B)))) := by
  have hn := K.gConj_nat h
  rw [gConj_top] at hn
  have hh := congrArg (fun k => comp (rightIn .conj (K.plug .top)) k) hn
  rw [← Laws.assoc, Laws.rightIn_Out, Laws.id_comp] at hh
  rw [← Laws.assoc (tensor .conj (id (K.plug .top)) h), Laws.tensor_comp,
    Laws.id_comp, ← fromTop_unique h (comp h (zero B))]
  exact hh

/-- (g epsilon), p.320, for any existing bottom-codomain arrow. -/
theorem gEpsilon {B : NormalForm P} (K : Context P) (h : Hom B .bot) :
    K.map h = comp (ofTerm (K.gDisj B))
      (comp (tensor .disj (id (K.plug .bot)) (zero B))
        (comp (tensor .disj (id (K.plug .bot)) h) (rightOut .disj (K.plug .bot)))) := by
  have hn := K.gDisj_nat h
  rw [gDisj_bot] at hn
  have hh := congrArg (fun k => comp k (rightOut .disj (K.plug .bot))) hn
  rw [Laws.assoc, Laws.rightIn_Out, Laws.comp_id] at hh
  rw [← Laws.assoc (tensor .disj (id (K.plug .bot)) (zero B)), Laws.tensor_comp,
    Laws.id_comp, ← toBot_unique h (comp (zero B) h)]
  simpa only [Laws.assoc] using hh

/-- (g eta f), p.320. -/
theorem gEta_comp {A B : NormalForm P} (K : Context P) (h : Hom .top B)
    (f : Hom A (K.plug .top)) :
    comp f (K.map h) = comp (rightIn .conj A)
      (comp (tensor .conj (id A) h)
        (comp (tensor .conj f (zero B)) (ofTerm (K.gConj B)))) := by
  rw [gEta, ← Laws.assoc f, ← Laws.rightIn_nat]
  simp only [Laws.assoc]
  rw [← Laws.assoc (tensor .conj f (id .top)), Laws.tensor_comp,
    Laws.comp_id, Laws.id_comp,
    ← Laws.assoc (tensor .conj f h), Laws.tensor_comp, Laws.comp_id,
    ← Laws.assoc (tensor .conj (id A) h), Laws.tensor_comp, Laws.id_comp]

/-- (g epsilon f), p.320. -/
theorem gEpsilon_comp {A B : NormalForm P} (K : Context P) (h : Hom B .bot)
    (f : Hom (K.plug .bot) A) :
    comp (K.map h) f = comp (ofTerm (K.gDisj B))
      (comp (tensor .disj f (zero B))
        (comp (tensor .disj (id A) h) (rightOut .disj A))) := by
  rw [gEpsilon]
  simp only [Laws.assoc]
  rw [Laws.rightOut_nat, ← Laws.assoc (tensor .disj (id (K.plug .bot)) h),
    Laws.tensor_comp, Laws.id_comp, Laws.comp_id,
    ← Laws.assoc (tensor .disj (id (K.plug .bot)) (zero B)), Laws.tensor_comp,
    Laws.id_comp, ← Laws.assoc (tensor .disj f (zero B)), Laws.tensor_comp, Laws.comp_id]

end Context
end DosenPetric.Reduced
