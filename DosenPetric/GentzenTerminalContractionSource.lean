module

public import DosenPetric.GentzenSequentialDisjFirstSource

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.SequentialRepair
universe u
variable {P : Type u}

theorem headParent_congr {F D : List (NormalForm P)} {C : NormalForm P}
    (g g' : G P (C::C::F) D) (he : ofTerm g.denote = ofTerm g'.denote) :
    ofTerm (headParent g).denote = ofTerm (headParent g').denote := by
  rw [headParent,headParent,ContractionBlock.denoteL,ContractionBlock.denoteL,he]

theorem terminal_source_denote {K F D : List (NormalForm P)} {C : NormalForm P}
    (r : Route K (F++[C])) (x : At K C) (a : At F C) (p : Route x.erase a.erase)
    (ha : r.firstBlock.get a = x) (hb : r.secondBlock.get (.here C []) = x)
    (hp : ∀ {E : NormalForm P} (v : At a.erase E),
      r.firstBlock.get (a.retain v) = x.retain (p.get v)) (g : G P (F++[C]) D) :
    comp (x.toHead.arrow .conj) (comp (r.sideArrow .conj) (ofTerm g.denote)) =
      ofTerm ((p.head C).program.left (headParent ((SequentialLogical.principal a C).left g))).denote := by
  have he := SequentialLogical.terminal_contraction_factor .conj r x a p ha hb hp
  change comp (x.toHead.arrow .conj) (r.sideArrow .conj) =
    comp ((p.head C).sideArrow .conj)
      (comp ((headBlock C a.erase).route.sideArrow .conj) ((SequentialLogical.principal a C).arrow .conj)) at he
  rw [StructuralProgram.left_denote,Route.program_arrow,headParent,ContractionBlock.denoteL,
    ExchangeScript.left_denote,← Laws.assoc,he]
  simp only [Laws.assoc]
  rfl

end DosenPetric.Reduced.Gentzen.SequentialRepair
