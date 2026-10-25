module

public import DosenPetric.GentzenChainedSelection
public import DosenPetric.GentzenReducibilityLogical

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

theorem Route.identity_side (o : Op) (Γ : List (NormalForm P)) :
    (Route.identity Γ).sideArrow o = (side P o).id (fold o Γ) := by
  apply side_ext o
  intro A a
  rw [Route.sideArrow_get,Route.get_identity,(side P o).id_comp]

namespace ContractionSelection
variable {C : NormalForm P} {F K : List (NormalForm P)}

theorem singleton_endpoints (p : ContractionSelection C F K) (h : p.arity = 1) : F = K := by
  induction p with
  | last => rfl
  | fixed A p ih => exact congrArg (List.cons A) (ih h)
  | more p => have hp := p.arity_pos; change p.arity+1=1 at h; omega

theorem singleton_get (p : ContractionSelection C F K) (h : p.arity = 1)
    {A : NormalForm P} (a : At F A) : p.route.get a = a.cast (p.singleton_endpoints h) := by
  apply At.index_injective
  rw [p.get_index,At.index_cast]
  have hr : p.rest = [] := by
    have hc := p.count
    change (p.first::p.rest).length = p.arity at hc
    rw [h] at hc
    exact List.eq_nil_iff_length_eq_zero.mpr (by simp only [List.length_cons] at hc; omega)
  change copyIndex (p.first::p.rest) a.index = a.index
  rw [hr]
  simp only [copyIndex,gaps,List.length_nil]
  repeat first | split | omega

theorem singleton_product (p : ContractionSelection C F F) (h : p.arity = 1) :
    ofTerm p.route.product = id (ante F) := by
  have he : p.route = Route.identity F := by
    apply Route.ext_get
    intro A a
    rw [Route.get_identity,p.singleton_get h]
    rfl
  rw [he]
  exact Route.identity_side .conj F

theorem singleton_coproduct (p : ContractionSelection C F F) (h : p.arity = 1) :
    ofTerm p.route.coproduct = id (succ F) := by
  have he : p.route = Route.identity F := by
    apply Route.ext_get
    intro A a
    rw [Route.get_identity,p.singleton_get h]
    rfl
  rw [he]
  exact Route.identity_side .disj F

/-- A singleton selection transports the context; two or more copies use the
    existing contraction constructor. No singleton proof node is introduced. -/
def performL (p : ContractionSelection C F K) (Δ : List (NormalForm P))
    (f : G P F Δ) : G P K Δ :=
  if h : 2 ≤ p.arity then p.block.applyL (by rw [p.count]; exact h) Δ f
  else f.reindex (p.singleton_endpoints (by have hp:=p.arity_pos; omega)) rfl

def performR (p : ContractionSelection C F K) (Γ : List (NormalForm P))
    (f : G P Γ F) : G P Γ K :=
  if h : 2 ≤ p.arity then p.block.applyR (by rw [p.count]; exact h) Γ f
  else f.reindex rfl (p.singleton_endpoints (by have hp:=p.arity_pos; omega))

theorem performL_denote (p : ContractionSelection C F K) (Δ : List (NormalForm P))
    (f : G P F Δ) :
    ofTerm (p.performL Δ f).denote = comp (ofTerm p.route.product) (ofTerm f.denote) := by
  unfold performL
  split
  · rw [p.block.denoteL,←p.route_eq]
  · rename_i hn
    have hs : p.arity = 1 := by have hp:=p.arity_pos; omega
    cases p.singleton_endpoints hs
    change ofTerm f.denote = _
    rw [p.singleton_product hs,Laws.id_comp]

theorem performR_denote (p : ContractionSelection C F K) (Γ : List (NormalForm P))
    (f : G P Γ F) :
    ofTerm (p.performR Γ f).denote = comp (ofTerm f.denote) (ofTerm p.route.coproduct) := by
  unfold performR
  split
  · rw [p.block.denoteR,←p.route_eq]
  · rename_i hn
    have hs : p.arity = 1 := by have hp:=p.arity_pos; omega
    cases p.singleton_endpoints hs
    change ofTerm f.denote = _
    rw [p.singleton_coproduct hs,Laws.comp_id]

theorem performL_count (p : ContractionSelection C F K) (Δ : List (NormalForm P))
    (f : G P F Δ) : (p.performL Δ f).cutCount = f.cutCount := by
  unfold performL
  split <;> simp only [ContractionBlock.countL,G.count_reindex]

theorem performR_count (p : ContractionSelection C F K) (Γ : List (NormalForm P))
    (f : G P Γ F) : (p.performR Γ f).cutCount = f.cutCount := by
  unfold performR
  split <;> simp only [ContractionBlock.countR,G.count_reindex]

theorem performL_atomized (p : ContractionSelection C F K) (Δ : List (NormalForm P))
    (f : G P F Δ) : (p.performL Δ f).Atomized ↔ f.Atomized := by
  unfold performL
  split <;> simp only [ContractionBlock.atomizedL,G.atomized_reindex]

theorem performR_atomized (p : ContractionSelection C F K) (Γ : List (NormalForm P))
    (f : G P Γ F) : (p.performR Γ f).Atomized ↔ f.Atomized := by
  unfold performR
  split <;> simp only [ContractionBlock.atomizedR,G.atomized_reindex]

end ContractionSelection
end DosenPetric.Reduced.Gentzen
