module

public import DosenPetric.GentzenCenteredSelection

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace SelectionMask
variable {C : NormalForm P} {F U K : List (NormalForm P)}

def picked : {F : List (NormalForm P)}→SelectionMask C F→{A : NormalForm P}→At F A→Bool
  | _,.fixed _ _,_,.here _ _=>false
  | _,.fixed _ m,_,.there a=>m.picked a
  | _,.pick _,_,.here _ _=>true
  | _,.pick m,_,.there a=>m.picked a

def offset : {F : List (NormalForm P)}→SelectionMask C F→{A : NormalForm P}→At F A→Nat
  | _,.fixed _ _,_,.here _ _=>0
  | _,.fixed _ m,_,.there a=>m.offset a+1
  | _,.pick _,_,.here _ _=>0
  | _,.pick m,_,.there a=>m.offset a

def canonical (m : SelectionMask C F) : Route (C::m.erased) F :=
  m.fill ((Route.identity m.erased).map (fun a=>a.there)) (.here C m.erased)

theorem fill_index (m : SelectionMask C F) (r : Route K m.erased) (c : At K C)
    (k : Nat) (hc : c.index=0)
    (hr : ∀ {A : NormalForm P} (a : At m.erased A),(r.get a).index=a.index+k)
    {A : NormalForm P} (a : At F A) :
    ((m.fill r c).get a).index=if m.picked a then 0 else m.offset a+k := by
  induction m generalizing k with
  | nil=>cases a
  | fixed B m ih=>
    cases r with | cons b r=>
      cases a with
      | here=>exact hr (.here _ m.erased)
      | there a=>
        have hh:=ih r (k+1) (fun {A} x=>by
          have h:=hr x.there
          change (r.get x).index=x.index+1+k at h
          omega) a
        simpa only [fill,Route.get,picked,offset,Nat.add_assoc,Nat.add_comm] using hh
  | pick m ih=>
    cases a with
    | here=>exact hc
    | there a=>exact ih r k hr a

theorem canonical_index (m : SelectionMask C F) {A : NormalForm P} (a : At F A) :
    (m.canonical.get a).index=if m.picked a then 0 else m.offset a+1 :=
  m.fill_index _ _ 1 rfl (fun a=>by simp only [Route.get_map,Route.get_identity,At.index]) a

theorem append_picked_before (m : SelectionMask C F) (n : SelectionMask C U)
    {A : NormalForm P} (a : At F A) : (m.append n).picked (a.before U)=m.picked a := by
  induction m with
  | nil=>cases a
  | fixed B m ih=>cases a with | here=>rfl | there a=>exact ih a
  | pick m ih=>cases a with | here=>rfl | there a=>exact ih a

theorem append_picked_shift (m : SelectionMask C F) (n : SelectionMask C U)
    {A : NormalForm P} (a : At U A) : (m.append n).picked (At.shift F a)=n.picked a := by
  induction m with
  | nil=>rfl
  | fixed B m ih=>exact ih
  | pick m ih=>exact ih

theorem append_offset_before (m : SelectionMask C F) (n : SelectionMask C U)
    {A : NormalForm P} (a : At F A) : (m.append n).offset (a.before U)=m.offset a := by
  induction m with
  | nil=>cases a
  | fixed B m ih=>cases a with | here=>rfl | there a=>exact congrArg (fun n=>n+1) (ih a)
  | pick m ih=>cases a with | here=>rfl | there a=>exact ih a

theorem append_offset_shift (m : SelectionMask C F) (n : SelectionMask C U)
    {A : NormalForm P} (a : At U A) :
    (m.append n).offset (At.shift F a)=m.erased.length+n.offset a := by
  induction m with
  | nil=>simp only [append,At.shift,erased,List.length_nil,Nat.zero_add]
  | fixed B m ih=>
    simp only [append,At.shift,offset,erased,List.length_cons]
    omega
  | pick m ih=>exact ih
end SelectionMask
end DosenPetric.Reduced.Gentzen

namespace DosenPetric.Reduced.Gentzen.SelectionMask
universe u
variable {P : Type u} {C : NormalForm P} {F : List (NormalForm P)}

theorem offset_lt (m : SelectionMask C F) {A : NormalForm P} (a : At F A)
    (h : m.picked a=false) : m.offset a<m.erased.length := by
  induction m with
  | nil=>cases a
  | fixed B m ih=>cases a with
    | here=>simp only [offset,erased,List.length_cons];omega
    | there a=>have hh:=ih a h;simp only [offset,erased,List.length_cons];omega
  | pick m ih=>cases a with
    | here=>cases h
    | there a=>exact ih a h

end DosenPetric.Reduced.Gentzen.SelectionMask
