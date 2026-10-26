module

public import DosenPetric.GentzenMaskExchange
public import DosenPetric.GentzenCenteredCoordinates

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace SelectionMask
variable {C : NormalForm P} {Γ X Y Θ : List (NormalForm P)}

theorem append_exists {F U : List (NormalForm P)} (m : SelectionMask C (F++U)) :
    ∃ (p : SelectionMask C F) (q : SelectionMask C U),p.append q=m := by
  obtain ⟨h⟩:=split_exists F U m
  cases h with | split p q=>exact ⟨p,q,rfl⟩

theorem quad_exists (m : SelectionMask C (Γ++X++Y++Θ)) :
    ∃ (g : SelectionMask C Γ) (x : SelectionMask C X) (y : SelectionMask C Y)
      (t : SelectionMask C Θ),quad g x y t=m := by
  obtain ⟨gxy,t,ht⟩:=append_exists m
  obtain ⟨gx,y,hy⟩:=append_exists gxy
  obtain ⟨g,x,hx⟩:=append_exists gx
  exact ⟨g,x,y,t,by rw [quad,hx,hy,ht]⟩

def swapFixed (g : SelectionMask C Γ) (x : SelectionMask C X)
    (y : SelectionMask C Y) (t : SelectionMask C Θ) :
    ExchangeScript P (C::(quad g y x t).erased) (C::(quad g x y t).erased) :=
  (ExchangeScript.exchange (C::g.erased) x.erased y.erased t.erased).reindex
    (by rw [quad_erased];rfl) (by rw [quad_erased];rfl)

theorem swapFixed_head (g : SelectionMask C Γ) (x : SelectionMask C X)
    (y : SelectionMask C Y) (t : SelectionMask C Θ) :
    (swapFixed g x y t).get (.here C _)=.here C _ := by
  apply At.index_injective
  change ((At.swapBlocks (C::g.erased) x.erased y.erased t.erased
    ((At.here C _).cast _)).cast _).index=0
  rw [At.index_cast,swapBlocks_index,At.index_cast]
  simp only [At.index,List.length_cons,exchangeIndex]
  exact ite_eq_left (by omega)

theorem swapFixed_index (g : SelectionMask C Γ) (x : SelectionMask C X)
    (y : SelectionMask C Y) (t : SelectionMask C Θ) {A : NormalForm P}
    (a : At (C::(quad g x y t).erased) A) :
    ((swapFixed g x y t).get a).index=
      exchangeIndex (g.erased.length+1) x.erased.length y.erased.length a.index := by
  change ((At.swapBlocks (C::g.erased) x.erased y.erased t.erased (a.cast _)).cast _).index=_
  rw [At.index_cast,swapBlocks_index,At.index_cast]
  rfl
end SelectionMask

namespace ContractionSelection
variable {C : NormalForm P} {F K : List (NormalForm P)}

def normalizeAs (p : ContractionSelection C F K) (m : SelectionMask C F) (h : p.mask=m) :
    ExchangeScript P (C::m.erased) K :=
  p.normalize.reindex (congrArg (fun m : SelectionMask C F=>C::m.erased) h) rfl

theorem normalizeAs_keep (p : ContractionSelection C F K) (m : SelectionMask C F) (h : p.mask=m) :
    (p.normalizeAs m h).get p.keep=.here C m.erased := by
  cases h;exact p.normalize_keep

theorem normalizeAs_index (p : ContractionSelection C F K) (m : SelectionMask C F) (h : p.mask=m)
    {A : NormalForm P} (a : At F A) :
    ((p.normalizeAs m h).get (p.route.get a)).index=
      (m.canonical.get a).index := by
  cases h
  exact (p.normalize_index a).trans (p.mask.canonical_index a).symm
end ContractionSelection

namespace UnrestrictedExchange
variable {C : NormalForm P} {Γ X Y Θ K : List (NormalForm P)}

/-- Complete positional factorization of an actual selection across exchange.
The exit contains only derived exchange nodes. Its lower endpoint is allowed
to differ because the last selected occurrence can move across the swap. -/
theorem factor (q : ContractionSelection C (Γ++Y++X++Θ) K) :
    ∃ (K0 : List (NormalForm P)) (p : ContractionSelection C (Γ++X++Y++Θ) K0)
      (r : ExchangeScript P K K0),
      p.arity=q.arity ∧ r.get p.keep=q.keep ∧
      (∀ {A : NormalForm P} (a : At (Γ++X++Y++Θ) A),
        q.route.get (a.swapBlocks Γ X Y Θ)=r.get (p.route.get a)) := by
  obtain ⟨g,y,x,t,hm⟩:=SelectionMask.quad_exists q.mask
  let m0:=SelectionMask.quad g x y t
  let m1:=SelectionMask.quad g y x t
  have hc : 0<m0.count := by
    have hq:=q.arity_pos
    have he:=q.mask_count
    rw [←hm,SelectionMask.quad_count] at he
    change 0<(SelectionMask.quad g x y t).count
    rw [SelectionMask.quad_count]
    omega
  obtain ⟨K0,p,hp⟩:=m0.selection_exists hc
  let u:=p.normalizeAs m0 hp
  let v:=q.normalizeAs m1 hm.symm
  let e:=SelectionMask.swapFixed g x y t
  let r:=v.inverse.seq (e.seq u)
  have hkeep : r.get p.keep=q.keep := by
    apply v.injective
    change v.get (v.inverse.get (e.get (u.get p.keep)))=v.get q.keep
    rw [v.get_inverse,p.normalizeAs_keep,SelectionMask.swapFixed_head,q.normalizeAs_keep]
  have hn : p.arity=q.arity := by
    have h0:=p.mask_count
    have h1:=q.mask_count
    rw [hp,SelectionMask.quad_count] at h0
    rw [←hm,SelectionMask.quad_count] at h1
    omega
  refine ⟨K0,p,r,hn,hkeep,?_⟩
  intro A a
  apply v.injective
  change v.get (q.route.get (a.swapBlocks Γ X Y Θ))=
    v.get (v.inverse.get (e.get (u.get (p.route.get a))))
  rw [v.get_inverse]
  apply At.index_injective
  rw [q.normalizeAs_index,SelectionMask.swapFixed_index,p.normalizeAs_index]
  exact SelectionMask.swap_canonical_index g x y t a
end UnrestrictedExchange
end DosenPetric.Reduced.Gentzen
