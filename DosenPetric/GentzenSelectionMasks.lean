module

public import DosenPetric.GentzenSelectionSplit

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

/-- A positional selection allowing an empty selected segment. A fixed slot
may have the same formula as a picked slot; the constructors distinguish them. -/
inductive SelectionMask (C : NormalForm P) : List (NormalForm P)→Type u where
  | nil : SelectionMask C []
  | fixed {F} (A : NormalForm P) : SelectionMask C F→SelectionMask C (A::F)
  | pick {F} : SelectionMask C F→SelectionMask C (C::F)

namespace SelectionMask
variable {C : NormalForm P} {F U K : List (NormalForm P)}

def allFixed : (F : List (NormalForm P))→SelectionMask C F
  | []=>.nil
  | A::F=>.fixed A (allFixed F)
def count : {F : List (NormalForm P)}→SelectionMask C F→Nat
  | _,.nil=>0
  | _,.fixed _ m=>m.count
  | _,.pick m=>m.count+1
@[reducible] def erased : {F : List (NormalForm P)}→SelectionMask C F→List (NormalForm P)
  | _,.nil=>[]
  | _,.fixed A m=>A::m.erased
  | _,.pick m=>m.erased
def selected : {F : List (NormalForm P)}→SelectionMask C F→List (At F C)
  | _,.nil=>[]
  | _,.fixed _ m=>m.selected.map At.there
  | _,.pick m=>.here C _::m.selected.map At.there

theorem allFixed_count (F : List (NormalForm P)) : (allFixed (C:=C) F).count=0 := by
  induction F with
  | nil=>rfl
  | cons A F ih=>exact ih

theorem allFixed_erased (F : List (NormalForm P)) : (allFixed (C:=C) F).erased=F := by
  induction F with
  | nil=>rfl
  | cons A F ih=>exact congrArg (List.cons A) ih

theorem allFixed_selected (F : List (NormalForm P)) : (allFixed (C:=C) F).selected=[] := by
  induction F with
  | nil=>rfl
  | cons A F ih=>simp only [allFixed,selected,ih,List.map_nil]

theorem selected_count (m : SelectionMask C F) : m.selected.length=m.count := by
  induction m with
  | nil=>rfl
  | fixed A m ih=>simpa only [selected,count,List.length_map] using ih
  | pick m ih=>simp only [selected,count,List.length_cons,List.length_map,ih]

theorem zero_fixed (m : SelectionMask C F) (h : m.count=0) : m=allFixed F := by
  induction m with
  | nil=>rfl
  | fixed A m ih=>exact congrArg (fixed A) (ih h)
  | pick m ih=>change m.count+1=0 at h;omega

def append : {F U : List (NormalForm P)}→SelectionMask C F→SelectionMask C U→SelectionMask C (F++U)
  | _,_,.nil,n=>n
  | _,_,.fixed A m,n=>.fixed A (m.append n)
  | _,_,.pick m,n=>.pick (m.append n)

theorem append_count (m : SelectionMask C F) (n : SelectionMask C U) : (m.append n).count=m.count+n.count := by
  induction m with
  | nil=>simp only [append,count,Nat.zero_add]
  | fixed A m ih=>exact ih
  | pick m ih=>simp only [append,count,ih];omega

theorem append_erased (m : SelectionMask C F) (n : SelectionMask C U) :
    (m.append n).erased=m.erased++n.erased := by
  induction m with
  | nil=>rfl
  | fixed A m ih=>exact congrArg (List.cons A) ih
  | pick m ih=>exact ih

/-- Fill fixed slots with their separately tagged route and all selected slots
with the distinguished anchor. This is data for existing structural arrows. -/
def fill : {F K : List (NormalForm P)}→(m : SelectionMask C F)→Route K m.erased→At K C→Route K F
  | _,_,m=>match m with
    | .nil=>fun _ _=>.nil
    | .fixed A m=>fun r c=>match r with
      | .cons a r=>.cons a (m.fill r c)
    | .pick m=>fun r c=>.cons c (m.fill r c)

theorem fill_map {T : List (NormalForm P)} (m : SelectionMask C F) (r : Route K m.erased)
    (c : At K C) (f : ∀ {A : NormalForm P}, At K A→At T A) :
    (m.fill r c).map f=m.fill (r.map f) (f c) := by
  induction m with
  | nil=>cases r;rfl
  | fixed A m ih=>cases r with | cons a r=>exact congrArg (Route.cons (f a)) (ih r)
  | pick m ih=>exact congrArg (Route.cons (f c)) (ih r)

inductive AppendSplit (C : NormalForm P) (F U : List (NormalForm P)) : SelectionMask C (F++U)→Type u where
  | split (m : SelectionMask C F) (n : SelectionMask C U) : AppendSplit C F U (m.append n)

theorem split_exists (F U : List (NormalForm P)) (m : SelectionMask C (F++U)) :
    Nonempty (AppendSplit C F U m) := by
  induction F with
  | nil=>exact ⟨.split .nil m⟩
  | cons A F ih=>
    cases m with
    | fixed A m=>
      obtain ⟨h⟩:=ih m
      cases h with | split a b=>exact ⟨.split (.fixed A a) b⟩
    | pick m=>
      obtain ⟨h⟩:=ih m
      cases h with | split a b=>exact ⟨.split (.pick a) b⟩
end SelectionMask

namespace ContractionSelection
variable {C : NormalForm P} {F K : List (NormalForm P)}

def mask : {F K : List (NormalForm P)}→ContractionSelection C F K→SelectionMask C F
  | _,_,.last Θ=>.pick (.allFixed Θ)
  | _,_,.fixed A p=>.fixed A p.mask
  | _,_,.more p=>.pick p.mask

theorem mask_count (p : ContractionSelection C F K) : p.mask.count=p.arity := by
  induction p with
  | last Θ=>simp only [mask,SelectionMask.count,SelectionMask.allFixed_count,arity]
  | fixed A p ih=>exact ih
  | more p ih=>exact congrArg (fun n=>n+1) ih

theorem mask_erased (p : ContractionSelection C F K) : p.mask.erased=p.erased := by
  induction p with
  | last Θ=>exact SelectionMask.allFixed_erased Θ
  | fixed A p ih=>exact congrArg (List.cons A) ih
  | more p ih=>exact ih

theorem mask_selected (p : ContractionSelection C F K) : p.mask.selected=p.selected := by
  induction p with
  | last Θ=>simp only [mask,SelectionMask.selected,SelectionMask.allFixed_selected,List.map_nil,selected]
  | fixed A p ih=>exact congrArg (List.map At.there) ih
  | more p ih=>exact congrArg (fun xs=>At.here C _::xs.map At.there) ih
end ContractionSelection
end DosenPetric.Reduced.Gentzen
