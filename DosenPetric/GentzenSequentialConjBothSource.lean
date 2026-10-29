module

public import DosenPetric.GentzenSequentialConjBothNative

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.SequentialConjBoth
universe u
variable {P : Type u}

theorem prepend_shared {Y V : List (NormalForm P)} (C : NormalForm P) (t : Route (C::Y) V) :
    Route.cons (.here C Y) t =
      (SequentialRepair.headBlock C Y).route.compose
        ((HeadRouting.front [C] Y C).route.compose (t.head C)) := by
  apply Route.ext_get
  intro E v
  rw [Route.compose_get,Route.compose_get,ExchangeScript.route_get]
  cases v with
  | here =>
    rw [Route.head_here]
    have hf := HeadRouting.front_before Y C (.here C [])
    change (HeadRouting.front [C] Y C).get (.here C (C::Y)) = .there (.here C Y) at hf
    rw [hf,SequentialRepair.headBlock_route]
    rfl
  | there v =>
    rw [Route.head_there]
    change t.get v = (SequentialRepair.headBlock C Y).route.get
      ((HeadRouting.front [C] Y C).get (t.get v).there)
    generalize t.get v = a
    cases a with
    | here =>
      have hf := HeadRouting.front_head [C] Y C
      change (HeadRouting.front [C] Y C).get (.there (.here C Y)) = .here C (C::Y) at hf
      rw [hf,SequentialRepair.headBlock_route]
      rfl
    | there a =>
      have hf := HeadRouting.front_tail [C] Y C a
      change (HeadRouting.front [C] Y C).get a.there.there = a.there.there at hf
      rw [hf,SequentialRepair.headBlock_route]
      rw [Route.get,Route.get,Route.get_map,Route.get_identity]

theorem front_factor {K F U : List (NormalForm P)} {C : NormalForm P}
    (r : Route K (C::(F++U))) (x : At K C) (a : At F C) (b : At U C)
    (p : Route x.erase a.erase) (q : Route x.erase b.erase)
    (hf : r.get (.here C (F++U)) = x)
    (ha : (r.secondBlock (F:=[C])).firstBlock.get a = x)
    (hb : (r.secondBlock (F:=[C])).secondBlock.get b = x)
    (hp : ∀ {E : NormalForm P} (v : At a.erase E),
      (r.secondBlock (F:=[C])).firstBlock.get (a.retain v) = x.retain (p.get v))
    (hq : ∀ {E : NormalForm P} (v : At b.erase E),
      (r.secondBlock (F:=[C])).secondBlock.get (b.retain v) = x.retain (q.get v)) :
    x.toHead.route.compose r =
      (SequentialRepair.headBlock C x.erase).route.compose
        ((HeadRouting.front [C] x.erase C).route.compose
          ((((p.head C).append (q.head C)).head C).compose
            ((a.toHead.route.parallel b.toHead.route).head C))) := by
  have hv := Route.selected_blocks_factor (r.secondBlock (F:=[C])) x a b p q ha hb hp hq
  have he : x.toHead.route.compose r =
      .cons (.here C x.erase) (x.toHead.route.compose (r.secondBlock (F:=[C]))) := by
    apply Route.ext_get
    intro E v
    rw [Route.compose_get,ExchangeScript.route_get]
    cases v with
    | here => rw [hf,At.toHead_get]; rfl
    | there v =>
      rw [Route.get,Route.compose_get,ExchangeScript.route_get,Route.secondBlock_get]
      rfl
  rw [he,prepend_shared,hv,← Route.head_compose]

theorem source_denote {K F U Γ Θ : List (NormalForm P)} {A B : NormalForm P}
    (r : Route K (.conj A B::(F++U))) (x : At K (.conj A B))
    (a : At F (.conj A B)) (b : At U (.conj A B))
    (p : Route x.erase a.erase) (q : Route x.erase b.erase)
    (hf : r.get (.here (.conj A B) (F++U)) = x)
    (ha : (r.secondBlock (F:=[.conj A B])).firstBlock.get a = x)
    (hb : (r.secondBlock (F:=[.conj A B])).secondBlock.get b = x)
    (hp : ∀ {E : NormalForm P} (v : At a.erase E),
      (r.secondBlock (F:=[.conj A B])).firstBlock.get (a.retain v) = x.retain (p.get v))
    (hq : ∀ {E : NormalForm P} (v : At b.erase E),
      (r.secondBlock (F:=[.conj A B])).secondBlock.get (b.retain v) = x.retain (q.get v))
    (f : G P Γ (A::F)) (g : G P Θ (B::U)) :
    comp (comp (ofTerm (G.conjR (Δ:=F) (Λ:=U) f g).denote) (r.sideArrow .disj)) (x.toHead.arrow .disj) =
      ofTerm (parent p q ((a.toHead.consFixed A).right f) ((b.toHead.consFixed B).right g)).denote := by
  have he := congrArg (fun t => t.sideArrow .disj) (front_factor r x a b p q hf ha hb hp hq)
  rw [Route.compose_side,ExchangeScript.route_arrow,Route.compose_side,Route.compose_side,
    Route.compose_side,ExchangeScript.route_arrow] at he
  dsimp only [side,opposite,category] at he
  rw [Laws.assoc,he,parent,SequentialRepair.headParentRight,ContractionBlock.denoteR,
    BlockedRightConj.headParent,ExchangeScript.right_denote,StructuralProgram.right_denote,Route.program_arrow]
  simp only [← Laws.assoc]
  rw [BlockedRightConj.script_conjR]
  rfl

end DosenPetric.Reduced.Gentzen.SequentialConjBoth
