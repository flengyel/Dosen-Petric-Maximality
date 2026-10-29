module

public import DosenPetric.GentzenSequentialDisjBothEquation

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.SequentialDisjBoth
universe u
variable {P : Type u}

theorem append_terminal {Y V : List (NormalForm P)} (C : NormalForm P) (t : Route (C::Y) V) :
    t.append (.cons (.here C Y) .nil) =
      (SequentialRepair.headBlock C Y).route.compose
        ((move C Y).route.compose (t.parallel (Route.identity [C]))) := by
  apply Route.ext_get
  intro E v
  cases At.cases_append V [C] v with
  | inl hv =>
    obtain ⟨v,rfl⟩ := hv
    rw [Route.append_before,Route.compose_get,Route.compose_get,Route.parallel_before,
      ExchangeScript.route_get]
    generalize t.get v = a
    cases a with
    | here => rw [At.before,move,ExchangeScript.consFixed_here,SequentialRepair.headBlock_route]; rfl
    | there a =>
      rw [At.before,move,ExchangeScript.consFixed_there,BinaryMix.swapWhole_before,
        SequentialRepair.headBlock_route]
      rw [At.shift,Route.get,Route.get,Route.get_map,Route.get_identity]
      rfl
  | inr hv =>
    obtain ⟨v,rfl⟩ := hv
    cases v with
    | here =>
      rw [Route.append_shift,Route.compose_get,Route.compose_get,Route.parallel_shift,
        Route.get_identity,ExchangeScript.route_get]
      rw [At.shift,move,ExchangeScript.consFixed_there,BinaryMix.swapWhole_shift,
        SequentialRepair.headBlock_route]
      rfl
    | there v => cases v

theorem terminal_factor {K F U : List (NormalForm P)} {C : NormalForm P}
    (r : Route K ((F++U)++[C])) (x : At K C) (a : At F C) (b : At U C)
    (p : Route x.erase a.erase) (q : Route x.erase b.erase)
    (ha : r.firstBlock.firstBlock.get a = x) (hb : r.firstBlock.secondBlock.get b = x)
    (hf : r.secondBlock.get (.here C []) = x)
    (hp : ∀ {E : NormalForm P} (v : At a.erase E),
      r.firstBlock.firstBlock.get (a.retain v) = x.retain (p.get v))
    (hq : ∀ {E : NormalForm P} (v : At b.erase E),
      r.firstBlock.secondBlock.get (b.retain v) = x.retain (q.get v)) :
    x.toHead.route.compose r =
      (SequentialRepair.headBlock C x.erase).route.compose
        ((move C x.erase).route.compose
          ((((p.head C).append (q.head C)).parallel (Route.identity [C])).compose
            ((a.toHead.route.parallel b.toHead.route).parallel (Route.identity [C])))) := by
  have hv := Route.selected_blocks_factor r.firstBlock x a b p q ha hb hp hq
  have he : x.toHead.route.compose r =
      (x.toHead.route.compose r.firstBlock).append (.cons (.here C x.erase) .nil) := by
    apply Route.ext_get
    intro E v
    cases At.cases_append (F++U) [C] v with
    | inl h =>
      obtain ⟨v,rfl⟩ := h
      rw [Route.compose_get,Route.append_before,Route.compose_get,Route.firstBlock_get]
    | inr h =>
      obtain ⟨v,rfl⟩ := h
      cases v with
      | here =>
        rw [Route.compose_get,Route.append_shift,← Route.secondBlock_get,hf,ExchangeScript.route_get,
          At.toHead_get]
        rfl
      | there v => cases v
  rw [he,append_terminal,hv,Route.parallel_compose_fixed]

/-- All three selected copies are compared before any recursive cut is made. -/
theorem source_denote {K F U D E : List (NormalForm P)} {A B : NormalForm P}
    (r : Route K ((F++U)++[.disj A B])) (x : At K (.disj A B))
    (a : At F (.disj A B)) (b : At U (.disj A B))
    (p : Route x.erase a.erase) (q : Route x.erase b.erase)
    (ha : r.firstBlock.firstBlock.get a = x) (hb : r.firstBlock.secondBlock.get b = x)
    (hf : r.secondBlock.get (.here (.disj A B) []) = x)
    (hp : ∀ {V : NormalForm P} (v : At a.erase V),
      r.firstBlock.firstBlock.get (a.retain v) = x.retain (p.get v))
    (hq : ∀ {V : NormalForm P} (v : At b.erase V),
      r.firstBlock.secondBlock.get (b.retain v) = x.retain (q.get v))
    (f : G P (F++[A]) D) (g : G P (U++[B]) E) :
    comp (x.toHead.arrow .conj) (comp (r.sideArrow .conj) (ofTerm (BlockedSource.disjLLast f g).denote)) =
      ofTerm (parent p q ((LogicalDeletion.headBefore a [A]).left f)
        ((LogicalDeletion.headBefore b [B]).left g)).denote := by
  have he := congrArg (fun t => t.sideArrow .conj) (terminal_factor r x a b p q ha hb hf hp hq)
  rw [Route.compose_side,ExchangeScript.route_arrow,Route.compose_side,Route.compose_side,
    Route.compose_side,ExchangeScript.route_arrow] at he
  dsimp only [side,category] at he
  rw [parent,SequentialRepair.headParent,ContractionBlock.denoteL,body,ExchangeScript.left_denote,
    BlockedLeftDisj.headParent,StructuralProgram.left_denote,Route.program_arrow]
  rw [← Laws.assoc (x.toHead.arrow .conj),he]
  simp only [Laws.assoc]
  apply congrArg (comp _)
  apply congrArg (comp _)
  apply congrArg (comp _)
  rw [Rules.terminalDisjLeft_denote]
  erw [Rules.terminalDisjLeft_nat]
  rw [Rules.terminalDisjLeft_denote]
  apply Rules.terminalDisjLeft_congr
  · simp only [ofTerm_comp,ExchangeScript.left_denote,LogicalDeletion.headBefore_route]
    rfl
  · simp only [ofTerm_comp,ExchangeScript.left_denote,LogicalDeletion.headBefore_route]
    rfl

end DosenPetric.Reduced.Gentzen.SequentialDisjBoth
