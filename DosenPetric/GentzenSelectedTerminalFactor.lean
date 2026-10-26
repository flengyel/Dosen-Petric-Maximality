module

public import DosenPetric.GentzenSelectedContextMasks

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.ContractionSelection
universe u
variable {P : Type u} {C : NormalForm P} {F K U L : List (NormalForm P)}

theorem prepend_mask (p : ContractionSelection C F K) (Ξ : List (NormalForm P)) :
    (p.prependFixed Ξ).mask=(SelectionMask.allFixed Ξ).append p.mask := by
  induction Ξ with
  | nil=>rfl
  | cons A Ξ ih=>exact congrArg (SelectionMask.fixed A) ih

theorem chain_mask (p : ContractionSelection C F K) (q : ContractionSelection C U L) :
    (p.chain q).mask=p.mask.append q.mask := by
  induction p with
  | last Θ=>
    change SelectionMask.pick (q.prependFixed Θ).mask=SelectionMask.pick _
    rw [q.prepend_mask]
  | fixed A p ih=>exact congrArg (SelectionMask.fixed A) ih
  | more p ih=>exact congrArg SelectionMask.pick ih

def normalizeTo (p : ContractionSelection C F K) (M : List (NormalForm P)) (h : p.mask.erased=M) :
    ExchangeScript P (C::M) K := p.normalize.reindex (congrArg (List.cons C) h) rfl

theorem normalizeTo_keep (p : ContractionSelection C F K) (M : List (NormalForm P)) (h : p.mask.erased=M) :
    (p.normalizeTo M h).get p.keep=.here C M := by
  apply At.index_injective
  change ((p.normalize.get p.keep).cast _).index=0
  rw [At.index_cast,p.normalize_keep]
  rfl

theorem normalizeTo_index (p : ContractionSelection C F K) (M : List (NormalForm P)) (h : p.mask.erased=M)
    {A : NormalForm P} (a : At F A) :
    ((p.normalizeTo M h).get (p.route.get a)).index=(p.mask.canonical.get a).index := by
  change ((p.normalize.get (p.route.get a)).cast _).index=_
  rw [At.index_cast,p.normalize_index,SelectionMask.canonical_index]
end ContractionSelection
namespace SelectedLogicalReducer
universe u
variable {P : Type u} {C : NormalForm P} {Γ Θ K L : List (NormalForm P)}
variable (g : SelectionMask C Γ) (t : SelectionMask C Θ)
variable (q : ContractionSelection C (Γ++C::Θ) K)
variable (p : ContractionSelection C (Γ++Θ) L)
variable (hq : q.mask=SelectionMask.selectedContext g t) (hp : p.mask=g.append t)

def terminal {F L : List (NormalForm P)} (p : ContractionSelection C F L) := p.chain (.last [])

include hp in
theorem terminal_mask : (terminal p).mask=SelectionMask.selectedTerminal g t := by
  rw [terminal,p.chain_mask,hp]
  rfl

include hq in
theorem original_erased : q.mask.erased=g.erased++t.erased := by
  rw [hq,SelectionMask.selectedContext_erased]

include hp in
theorem terminal_erased : (terminal p).mask.erased=g.erased++t.erased := by
  rw [terminal_mask g t p hp,SelectionMask.selectedTerminal_erased]

def exit : ExchangeScript P K (p.erased++[C]) :=
  (q.normalizeTo _ (original_erased g t q hq)).inverse.seq
    ((terminal p).normalizeTo _ (terminal_erased g t p hp))

theorem exit_keep : (exit g t q p hq hp).get (terminal p).keep=q.keep := by
  apply (q.normalizeTo _ (original_erased g t q hq)).injective
  change (q.normalizeTo _ _).get ((q.normalizeTo _ _).inverse.get
    (((terminal p).normalizeTo _ _).get (terminal p).keep))=(q.normalizeTo _ _).get q.keep
  rw [ExchangeScript.get_inverse,ContractionSelection.normalizeTo_keep,ContractionSelection.normalizeTo_keep]

theorem exit_square {A : NormalForm P} (a : At (Γ++C::Θ) A) :
    q.route.get a=(exit g t q p hq hp).get
      ((terminal p).route.get ((Route.moveEnd Γ [C] Θ).get a)) := by
  let v:=q.normalizeTo _ (original_erased g t q hq)
  apply v.injective
  change v.get (q.route.get a)=v.get (v.inverse.get
    (((terminal p).normalizeTo _ _).get ((terminal p).route.get ((Route.moveEnd Γ [C] Θ).get a))))
  rw [v.get_inverse]
  apply At.index_injective
  rw [q.normalizeTo_index,ContractionSelection.normalizeTo_index,hq,terminal_mask g t p hp]
  exact SelectionMask.selected_terminal_index g t a
end SelectedLogicalReducer
end DosenPetric.Reduced.Gentzen
