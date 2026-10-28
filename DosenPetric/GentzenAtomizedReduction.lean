module

public import DosenPetric.GentzenParameterizedRouteRepair

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u} {C : NormalForm P} {Γ Δ Θ Λ U V : List (NormalForm P)}
variable {f : G P Γ (C::Δ)} {g : G P (C::Θ) Λ} {w h : G P U V}

/-- A single replacement satisfies atomization, equality and every rebuilt
eligible-descendant bound on atomized inputs. -/
def AtomizedReducesL (f : G P Γ (C::Δ)) (g : G P (C::Θ) Λ)
    (w : G P U V) (x : At U C) : Prop :=
  w.Atomized → ∀ (a : ProofAddress g w), ReducibleL f g a x →
    ∃ h : G P U V, h.CutFree ∧ h.Atomized ∧ ofTerm h.denote=ofTerm w.denote ∧
      ∀ {I J : List (NormalForm P)} {v : G P I J} (b : ProofAddress h v) (y : At I C),
        ReducibleL f (a.replace h) ((a.inserted h).append b) y → v.rho .left y < w.rho .left x

/-- The independently typed right replacement statement. -/
def AtomizedReducesR (f : G P Γ (C::Δ)) (g : G P (C::Θ) Λ)
    (w : G P U V) (x : At V C) : Prop :=
  w.Atomized → ∀ (a : ProofAddress f w), ReducibleR f g a x →
    ∃ h : G P U V, h.CutFree ∧ h.Atomized ∧ ofTerm h.denote=ofTerm w.denote ∧
      ∀ {I J : List (NormalForm P)} {v : G P I J} (b : ProofAddress h v) (y : At J C),
        ReducibleR (a.replace h) g ((a.inserted h).append b) y → v.rho .right y < w.rho .right x

theorem AtomizedReducesL.of_strict (x : At U C) (hc : w.CutFree → h.CutFree)
    (ha : w.Atomized → h.Atomized) (he : ofTerm h.denote=ofTerm w.denote)
    (hk : h.rho .left x < w.rho .left x) : AtomizedReducesL f g w x := by
  intro hw a hr
  exact ⟨h,hc hr.cutFree,ha hw,he,fun b y hv => ReducibilityBoundary.strict_left a x hr hk b y hv⟩

theorem AtomizedReducesR.of_strict (x : At V C) (hc : w.CutFree → h.CutFree)
    (ha : w.Atomized → h.Atomized) (he : ofTerm h.denote=ofTerm w.denote)
    (hk : h.rho .right x < w.rho .right x) : AtomizedReducesR f g w x := by
  intro hw a hr
  exact ⟨h,hc hr.cutFree,ha hw,he,fun b y hv => ReducibilityBoundary.strict_right a x hr hk b y hv⟩

namespace ContractionSelection
variable {F K L : List (NormalForm P)}

theorem factor_route_support (q : ContractionSelection C U K) (r : Route U F)
    (p : ContractionSelection C F L) (s : Route q.mask.erased p.mask.erased)
    (hs : ∀ {A : NormalForm P} (a : At F A),
      q.route.get (r.get a)=q.normalize.inverse.get
        ((s.program.consFixed C).get (p.normalize.get (p.route.get a))))
    (hr : r.AtomicOmissions) : s.AtomicOmissions := by
  let T := (r.map q.route.get).map q.normalize.get
  have he : T = (p.route.map p.normalize.get).map (s.program.consFixed C).get := by
    apply Route.ext_get
    intro A a
    simp only [T,Route.get_map,hs,q.normalize.get_inverse]
  intro A a ha
  exact T.factor_atomicOmissions (Route.selection_atomicOmissions q r hr) p s he a ha

theorem factor_route_preimage (q : ContractionSelection C U K) (r : Route U F)
    (p : ContractionSelection C F L) (s : Route q.mask.erased p.mask.erased)
    (hs : ∀ {A : NormalForm P} (a : At F A),
      q.route.get (r.get a)=q.normalize.inverse.get
        ((s.program.consFixed C).get (p.normalize.get (p.route.get a))))
    {A : NormalForm P} (a : At q.mask.erased A) :
    (∃ b : At p.mask.erased A, s.get b=a) ↔
      (∃ z : At F A, q.normalize.get (q.route.get (r.get z))=a.there) := by
  let T := (r.map q.route.get).map q.normalize.get
  have he : T = (p.route.map p.normalize.get).map (s.program.consFixed C).get := by
    apply Route.ext_get
    intro A a
    simp only [T,Route.get_map,hs,q.normalize.get_inverse]
  simpa only [T,Route.get_map] using T.factor_preimage p s he a
end ContractionSelection
end DosenPetric.Reduced.Gentzen
