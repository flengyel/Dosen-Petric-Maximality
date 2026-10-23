module

public import DosenPetric.GentzenGapLogicalPositions
public import DosenPetric.GentzenSameSideExchangeFixedRanks

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.G
universe u
variable {P : Type u}

theorem predecessors_conjL_surviving (Γ Θ Δ : List (NormalForm P)) (A B : NormalForm P)
    (f : G P (Γ ++ A :: B :: Θ) Δ) {E : NormalForm P}
    (a : At (Γ ++ A :: B :: Θ) E) (b : At (Γ ++ .conj A B :: Θ) E)
    (hp : At.fixed Γ [A,B] [.conj A B] Θ a = some b) :
    (conjL Γ Θ Δ A B f).predecessors .left b = [⟨⟨_,_,f,Premise.conjL Γ Θ Δ A B f⟩,a⟩] := by
  have hf : ((Premise.conjL Γ Θ Δ A B f).route .left).fiber b = [a] := by
    change (TraceRoute.ofMap _ _ (At.fixed Γ [A,B] [.conj A B] Θ)).fiber b = [a]
    exact (TraceRoute.fiber_fixed Γ [A,B] [.conj A B] Θ b).trans
      (congrArg Option.toList ((At.fixed_reverse Γ [A,B] [.conj A B] Θ a b).mp hp))
  simp only [predecessors,branches,List.flatMap_cons,List.flatMap_nil,List.append_nil]
  exact congrArg (fun us : List (At (Γ ++ A :: B :: Θ) E) =>
    us.map (fun y => (⟨⟨_,_,f,Premise.conjL Γ Θ Δ A B f⟩,y⟩ : Upper (conjL Γ Θ Δ A B f) .left E))) hf

theorem predecessors_disjR_surviving (Γ Δ Λ : List (NormalForm P)) (A B : NormalForm P)
    (f : G P Γ (Δ ++ A :: B :: Λ)) {E : NormalForm P}
    (a : At (Δ ++ A :: B :: Λ) E) (b : At (Δ ++ .disj A B :: Λ) E)
    (hp : At.fixed Δ [A,B] [.disj A B] Λ a = some b) :
    (disjR Γ Δ Λ A B f).predecessors .right b = [⟨⟨_,_,f,Premise.disjR Γ Δ Λ A B f⟩,a⟩] := by
  have hf : ((Premise.disjR Γ Δ Λ A B f).route .right).fiber b = [a] := by
    change (TraceRoute.ofMap _ _ (At.fixed Δ [A,B] [.disj A B] Λ)).fiber b = [a]
    exact (TraceRoute.fiber_fixed Δ [A,B] [.disj A B] Λ b).trans
      (congrArg Option.toList ((At.fixed_reverse Δ [A,B] [.disj A B] Λ a b).mp hp))
  simp only [predecessors,branches,List.flatMap_cons,List.flatMap_nil,List.append_nil]
  exact congrArg (fun us : List (At (Δ ++ A :: B :: Λ) E) =>
    us.map (fun y => (⟨⟨_,_,f,Premise.disjR Γ Δ Λ A B f⟩,y⟩ : Upper (disjR Γ Δ Λ A B f) .right E))) hf

theorem rho_conjL_surviving (Γ Θ Δ : List (NormalForm P)) (A B : NormalForm P)
    (f : G P (Γ ++ A :: B :: Θ) Δ) {E : NormalForm P}
    (a : At (Γ ++ A :: B :: Θ) E) (b : At (Γ ++ .conj A B :: Θ) E)
    (hp : At.fixed Γ [A,B] [.conj A B] Θ a = some b) :
    (conjL Γ Θ Δ A B f).rho .left b = 1 + f.rho .left a := by
  have h := congrArg (fun us : List (Upper (conjL Γ Θ Δ A B f) .left E) =>
    1 + (us.map (fun v => v.branch.proof.rho .left v.position)).sum)
    (predecessors_conjL_surviving Γ Θ Δ A B f a b hp)
  exact ((conjL Γ Θ Δ A B f).rho_eq .left b).trans
    (by simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] using h)

theorem rho_disjR_surviving (Γ Δ Λ : List (NormalForm P)) (A B : NormalForm P)
    (f : G P Γ (Δ ++ A :: B :: Λ)) {E : NormalForm P}
    (a : At (Δ ++ A :: B :: Λ) E) (b : At (Δ ++ .disj A B :: Λ) E)
    (hp : At.fixed Δ [A,B] [.disj A B] Λ a = some b) :
    (disjR Γ Δ Λ A B f).rho .right b = 1 + f.rho .right a := by
  have h := congrArg (fun us : List (Upper (disjR Γ Δ Λ A B f) .right E) =>
    1 + (us.map (fun v => v.branch.proof.rho .right v.position)).sum)
    (predecessors_disjR_surviving Γ Δ Λ A B f a b hp)
  exact ((disjR Γ Δ Λ A B f).rho_eq .right b).trans
    (by simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] using h)

end DosenPetric.Reduced.Gentzen.G
