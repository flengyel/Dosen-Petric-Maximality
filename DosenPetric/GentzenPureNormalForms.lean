module

public import DosenPetric.GentzenPureEdgeEvaluation

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

/-- A finite union of literal paths at the original endpoints, with a witnessed zero. -/
def HasPureNormalForm {A B : NormalForm P} (f : Hom A B) : Prop :=
  ∃ es : List (PureEdge A B), f = PureEdge.evaluate f es

namespace HasPureNormalForm
variable {A B : NormalForm P}

theorem congr {f g : Hom A B} (h : f = g) (hf : HasPureNormalForm f) : HasPureNormalForm g := by
  cases h
  exact hf

theorem edge (e : PureEdge A B) : HasPureNormalForm e.arrow :=
  ⟨[e],(finiteUnion.singleton e.arrow e.arrow).symm⟩

theorem zero (w : Hom A B) : HasPureNormalForm (zeroOf w) :=
  ⟨[],(zeroOf_independent (zeroOf w) w).symm⟩

theorem union {f g : Hom A B} (hf : HasPureNormalForm f) (hg : HasPureNormalForm g) :
    HasPureNormalForm (Reduced.union f g) := by
  obtain ⟨es,he⟩ := hf
  obtain ⟨ds,hd⟩ := hg
  refine ⟨es ++ ds,?_⟩
  change Reduced.union f g = finiteUnion (Reduced.union f g) ((es ++ ds).map PureEdge.arrow)
  rw [List.map_append,finiteUnion.append]
  have ef : f = finiteUnion (Reduced.union f g) (es.map PureEdge.arrow) :=
    he.trans (finiteUnion.witness_independent f (Reduced.union f g) _)
  have eg : g = finiteUnion (Reduced.union f g) (ds.map PureEdge.arrow) :=
    hd.trans (finiteUnion.witness_independent g (Reduced.union f g) _)
  exact congrArgTwo Reduced.union ef eg

/-- Precomposition transports each original source port; no relation reflection is used. -/
theorem pre {X : NormalForm P} (h : Hom X A) {f : Hom A B} (hf : HasPureNormalForm f)
    (hp : ∀ (l : Literal P) (p : PurePort .conj A l),
      ∃ q : PurePort .conj X l, comp h p.arrow = q.arrow) : HasPureNormalForm (comp h f) := by
  obtain ⟨es,he⟩ := hf
  let next : PureEdge A B → PureEdge X B := fun e =>
    ⟨e.label,Classical.choose (hp e.label e.source),e.target⟩
  have hn (e : PureEdge A B) : comp h e.arrow = (next e).arrow := by
    rw [PureEdge.arrow,← Laws.assoc,Classical.choose_spec (hp e.label e.source)]
    rfl
  refine ⟨es.map next,?_⟩
  calc
    comp h f = comp h (PureEdge.evaluate f es) := congrArg (comp h) he
    _ = finiteUnion (comp h f) ((es.map PureEdge.arrow).map (comp h)) := finiteUnion.pre h f _
    _ = PureEdge.evaluate (comp h f) (es.map next) := by
      simp only [PureEdge.evaluate,List.map_map]
      congr 1
      apply List.map_congr_left
      intro e _
      exact hn e

/-- The coproduct target ports are transported with their separately typed variance. -/
theorem post {Y : NormalForm P} {f : Hom A B} (hf : HasPureNormalForm f) (h : Hom B Y)
    (hp : ∀ (l : Literal P) (p : PurePort .disj B l),
      ∃ q : PurePort .disj Y l, comp p.arrow h = q.arrow) : HasPureNormalForm (comp f h) := by
  obtain ⟨es,he⟩ := hf
  let next : PureEdge A B → PureEdge A Y := fun e =>
    ⟨e.label,e.source,Classical.choose (hp e.label e.target)⟩
  have hn (e : PureEdge A B) : comp e.arrow h = (next e).arrow := by
    rw [PureEdge.arrow,Laws.assoc,Classical.choose_spec (hp e.label e.target)]
    rfl
  refine ⟨es.map next,?_⟩
  calc
    comp f h = comp (PureEdge.evaluate f es) h := congrArg (fun k => comp k h) he
    _ = finiteUnion (comp f h) ((es.map PureEdge.arrow).map (fun k => comp k h)) := finiteUnion.post f _ h
    _ = PureEdge.evaluate (comp f h) (es.map next) := by
      simp only [PureEdge.evaluate,List.map_map]
      congr 1
      apply List.map_congr_left
      intro e _
      exact hn e

theorem faithful {f g : Hom A B} (hf : HasPureNormalForm f) (hg : HasPureNormalForm g)
    (h : occurrenceMap f = occurrenceMap g) : f = g := by
  obtain ⟨es,he⟩ := hf
  obtain ⟨ds,hd⟩ := hg
  have hr : occurrenceMap (PureEdge.evaluate f es) = occurrenceMap (PureEdge.evaluate g ds) := by
    rw [← he,← hd,h]
  exact he.trans ((PureEdge.evaluate_faithful f g es ds hr).trans hd.symm)

end HasPureNormalForm
end DosenPetric.Reduced.Gentzen
