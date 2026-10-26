module

public import DosenPetric.GentzenTerminalSourceOneRanks

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.W6.TerminalOne
universe u
variable {P : Type u} {A B : NormalForm P} {F K U L Δ Λ : List (NormalForm P)}
section First
variable (p : ContractionSelection (.disj A B) F K) (f : G P (F++[A]) Δ) (g : G P (U++[B]) Λ)

theorem addressedFirst {Φ Ξ Ω Ψ : List (NormalForm P)}
    {cutLeft : G P Φ (.disj A B::Ξ)} {root : G P (.disj A B::Ω) Ψ}
    (a : ProofAddress root (oldFirst p f g))
    (hr : ReducibleL cutLeft root a (p.extend U).lastKeep) :
    (repairFirst p f g).CutFree ∧
    ofTerm (repairFirst p f g).denote=ofTerm (oldFirst p f g).denote ∧
    ofTerm (a.replace (repairFirst p f g)).denote=ofTerm root.denote ∧
    ∀ {I J : List (NormalForm P)} {v : G P I J} (b : ProofAddress (repairFirst p f g) v)
      (y : At I (.disj A B)),
      ReducibleL cutLeft (a.replace (repairFirst p f g)) ((a.inserted _).append b) y →
        v.rho .left y<(oldFirst p f g).rho .left (p.extend U).lastKeep := by
  have he:=denoteFirst p f g
  refine ⟨(cutFreeFirst p f g).mpr hr.cutFree,he,a.replace_denote _ he,?_⟩
  intro I J v b y hv
  exact ReducibilityBoundary.descendants_left a (p.extend U).lastKeep _ (blockedFirst p f g)
    (fun z hz=>hr.entry_unique z hz) (endpoint_leFirst p f g) b y hv

theorem reducesFirst {Φ Ξ Ω Ψ : List (NormalForm P)}
    (cutLeft : G P Φ (.disj A B::Ξ)) (root : G P (.disj A B::Ω) Ψ) :
    ReducesL cutLeft root (oldFirst p f g) (p.extend U).lastKeep := by
  intro a hr
  have h:=addressedFirst p f g a hr
  exact ⟨repairFirst p f g,h.1,h.2.1,h.2.2.2⟩
end First
section Second
variable (q : ContractionSelection (.disj A B) U L) (f : G P (F++[A]) Δ) (g : G P (U++[B]) Λ)

theorem addressedSecond {Φ Ξ Ω Ψ : List (NormalForm P)}
    {cutLeft : G P Φ (.disj A B::Ξ)} {root : G P (.disj A B::Ω) Ψ}
    (a : ProofAddress root (oldSecond q f g))
    (hr : ReducibleL cutLeft root a (q.prependFixed F).lastKeep) :
    (repairSecond q f g).CutFree ∧
    ofTerm (repairSecond q f g).denote=ofTerm (oldSecond q f g).denote ∧
    ofTerm (a.replace (repairSecond q f g)).denote=ofTerm root.denote ∧
    ∀ {I J : List (NormalForm P)} {v : G P I J} (b : ProofAddress (repairSecond q f g) v)
      (y : At I (.disj A B)),
      ReducibleL cutLeft (a.replace (repairSecond q f g)) ((a.inserted _).append b) y →
        v.rho .left y<(oldSecond q f g).rho .left (q.prependFixed F).lastKeep := by
  have he:=denoteSecond q f g
  refine ⟨(cutFreeSecond q f g).mpr hr.cutFree,he,a.replace_denote _ he,?_⟩
  intro I J v b y hv
  exact ReducibilityBoundary.descendants_left a (q.prependFixed F).lastKeep _ (blockedSecond q f g)
    (fun z hz=>hr.entry_unique z hz) (endpoint_leSecond q f g) b y hv

theorem reducesSecond {Φ Ξ Ω Ψ : List (NormalForm P)}
    (cutLeft : G P Φ (.disj A B::Ξ)) (root : G P (.disj A B::Ω) Ψ) :
    ReducesL cutLeft root (oldSecond q f g) (q.prependFixed F).lastKeep := by
  intro a hr
  have h:=addressedSecond q f g a hr
  exact ⟨repairSecond q f g,h.1,h.2.1,h.2.2.2⟩
end Second
end DosenPetric.Reduced.Gentzen.W6.TerminalOne
