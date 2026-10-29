module

public import DosenPetric.GentzenPurePortRelations

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.PureEdge
universe u
variable {P : Type u} {A B : NormalForm P}

theorem ext_positions (e d : PureEdge A B)
    (hs : e.source.position = d.source.position)
    (ht : e.target.position = d.target.position) : e = d := by
  cases e with
  | mk l a b =>
    cases d with
    | mk m c d =>
      have hl : l = m := PurePort.label_of_position_eq a c hs
      cases hl
      have ha := PurePort.position_injective a c hs
      have hb := PurePort.position_injective b d ht
      cases ha
      cases hb
      rfl

/-- Finite atomic normal forms use a zero only in the witnessed ambient hom-set. -/
def evaluate (w : Hom A B) (es : List (PureEdge A B)) : Hom A B :=
  finiteUnion w (es.map arrow)

theorem evaluate_relation (w : Hom A B) (es : List (PureEdge A B))
    (x : A.formula.Occ) (y : B.formula.Occ) :
    occurrenceMap (evaluate w es) x y ↔
      ∃ e ∈ es, x = e.source.position ∧ y = e.target.position := by
  rw [evaluate,finiteUnion.occurrence]
  constructor
  · rintro ⟨f,hf,hr⟩
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp hf
    exact ⟨e,he,(relation e x y).mp hr⟩
  · rintro ⟨e,he,hr⟩
    exact ⟨e.arrow,List.mem_map.mpr ⟨e,he,rfl⟩,(relation e x y).mpr hr⟩

theorem member_iff (w : Hom A B) (es : List (PureEdge A B)) (e : PureEdge A B) :
    e ∈ es ↔ occurrenceMap (evaluate w es) e.source.position e.target.position := by
  rw [evaluate_relation]
  constructor
  · intro he; exact ⟨e,he,rfl,rfl⟩
  · rintro ⟨d,hd,hs,ht⟩
    cases ext_positions e d hs ht
    exact hd

/-- Exact relation equality determines every finite atomic normal form. This
does not assume that all positive arrows already have such a form. -/
theorem evaluate_faithful (w v : Hom A B) (es ds : List (PureEdge A B))
    (h : occurrenceMap (evaluate w es) = occurrenceMap (evaluate v ds)) :
    evaluate w es = evaluate v ds := by
  apply finiteUnion.eq_of_members
  intro f
  constructor
  · intro hf
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp hf
    have hr := (member_iff w es e).mp he
    rw [h] at hr
    exact List.mem_map.mpr ⟨e,(member_iff v ds e).mpr hr,rfl⟩
  · intro hf
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp hf
    have hr := (member_iff v ds e).mp he
    rw [← h] at hr
    exact List.mem_map.mpr ⟨e,(member_iff w es e).mpr hr,rfl⟩

end DosenPetric.Reduced.Gentzen.PureEdge
