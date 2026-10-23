module

public import DosenPetric.GentzenGapExchangeData
public import DosenPetric.GentzenFixedContractionRanks

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

namespace At

theorem swapBlocks_inverse (Γ X Y Θ : List (NormalForm P)) {A : NormalForm P}
    (a : At (Γ ++ X ++ Y ++ Θ) A) :
    (a.swapBlocks Γ X Y Θ).swapBlocks Γ Y X Θ = a := by
  apply index_injective
  rw [swapBlocks_index,swapBlocks_index]
  exact GapExchange.exchange_inverse ..

theorem swapBlocks_injective (Γ X Y Θ : List (NormalForm P)) {A : NormalForm P}
    (a b : At (Γ ++ X ++ Y ++ Θ) A)
    (h : a.swapBlocks Γ X Y Θ = b.swapBlocks Γ X Y Θ) : a = b := by
  have he := congrArg (fun x => x.swapBlocks Γ Y X Θ) h
  simpa only [swapBlocks_inverse] using he

end At

theorem exchangeL_projection (Γ X Y Θ : List (NormalForm P)) {A : NormalForm P}
    (a : At (Γ ++ X ++ Y ++ Θ) A) :
    comp (ofTerm (exchange .conj Γ X Y Θ).invTerm) (ofTerm a.projection) =
      ofTerm (a.swapBlocks Γ X Y Θ).projection := exchangeBack_component .conj Γ X Y Θ a

theorem exchangeR_injection (Γ X Y Θ : List (NormalForm P)) {A : NormalForm P}
    (a : At (Γ ++ X ++ Y ++ Θ) A) :
    comp (ofTerm a.injection) (ofTerm (exchange .disj Γ X Y Θ).toTerm) =
      ofTerm (a.swapBlocks Γ X Y Θ).injection := exchangeBack_component .disj Γ X Y Θ a

namespace G

theorem predecessors_exchangeL_embedded (Γ X Y Θ Δ : List (NormalForm P))
    (f : G P (Γ ++ X ++ Y ++ Θ) Δ) {A : NormalForm P} (a : At (Γ ++ X ++ Y ++ Θ) A) :
    (exchangeL Γ X Y Θ Δ f).predecessors .left (a.swapBlocks Γ X Y Θ) =
      [⟨⟨_,_,f,Premise.exchangeL Γ X Y Θ Δ f⟩,a⟩] := by
  have hf : ((Premise.exchangeL Γ X Y Θ Δ f).route .left).fiber (a.swapBlocks Γ X Y Θ) = [a] := by
    apply TraceRoute.fiber_single
    intro b
    have hr := (Premise.exchangeL Γ X Y Θ Δ f).route_correct .left b
    change _ = some (b.swapBlocks Γ X Y Θ) at hr
    constructor
    · intro h
      exact At.swapBlocks_injective Γ X Y Θ b a (Option.some.inj (hr.symm.trans h))
    · intro h
      cases h
      exact hr
  simp only [predecessors,branches,List.flatMap_cons,List.flatMap_nil,List.append_nil]
  exact congrArg (fun us : List (At (Γ ++ X ++ Y ++ Θ) A) =>
    us.map (fun y => (⟨⟨_,_,f,Premise.exchangeL Γ X Y Θ Δ f⟩,y⟩ : Upper (exchangeL Γ X Y Θ Δ f) .left A))) hf

theorem predecessors_exchangeR_embedded (Γ Δ X Y Λ : List (NormalForm P))
    (f : G P Γ (Δ ++ X ++ Y ++ Λ)) {A : NormalForm P} (a : At (Δ ++ X ++ Y ++ Λ) A) :
    (exchangeR Γ Δ X Y Λ f).predecessors .right (a.swapBlocks Δ X Y Λ) =
      [⟨⟨_,_,f,Premise.exchangeR Γ Δ X Y Λ f⟩,a⟩] := by
  have hf : ((Premise.exchangeR Γ Δ X Y Λ f).route .right).fiber (a.swapBlocks Δ X Y Λ) = [a] := by
    apply TraceRoute.fiber_single
    intro b
    have hr := (Premise.exchangeR Γ Δ X Y Λ f).route_correct .right b
    change _ = some (b.swapBlocks Δ X Y Λ) at hr
    constructor
    · intro h
      exact At.swapBlocks_injective Δ X Y Λ b a (Option.some.inj (hr.symm.trans h))
    · intro h
      cases h
      exact hr
  simp only [predecessors,branches,List.flatMap_cons,List.flatMap_nil,List.append_nil]
  exact congrArg (fun us : List (At (Δ ++ X ++ Y ++ Λ) A) =>
    us.map (fun y => (⟨⟨_,_,f,Premise.exchangeR Γ Δ X Y Λ f⟩,y⟩ : Upper (exchangeR Γ Δ X Y Λ f) .right A))) hf

theorem rho_exchangeL_embedded (Γ X Y Θ Δ : List (NormalForm P))
    (f : G P (Γ ++ X ++ Y ++ Θ) Δ) {A : NormalForm P} (a : At (Γ ++ X ++ Y ++ Θ) A) :
    (exchangeL Γ X Y Θ Δ f).rho .left (a.swapBlocks Γ X Y Θ) = 1 + f.rho .left a := by
  have he := congrArg (fun us : List (Upper (exchangeL Γ X Y Θ Δ f) .left A) =>
    1 + (us.map (fun v => v.branch.proof.rho .left v.position)).sum)
    (predecessors_exchangeL_embedded Γ X Y Θ Δ f a)
  exact ((exchangeL Γ X Y Θ Δ f).rho_eq .left _).trans
    (by simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] using he)

theorem rho_exchangeR_embedded (Γ Δ X Y Λ : List (NormalForm P))
    (f : G P Γ (Δ ++ X ++ Y ++ Λ)) {A : NormalForm P} (a : At (Δ ++ X ++ Y ++ Λ) A) :
    (exchangeR Γ Δ X Y Λ f).rho .right (a.swapBlocks Δ X Y Λ) = 1 + f.rho .right a := by
  have he := congrArg (fun us : List (Upper (exchangeR Γ Δ X Y Λ f) .right A) =>
    1 + (us.map (fun v => v.branch.proof.rho .right v.position)).sum)
    (predecessors_exchangeR_embedded Γ Δ X Y Λ f a)
  exact ((exchangeR Γ Δ X Y Λ f).rho_eq .right _).trans
    (by simpa only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] using he)

end G
end DosenPetric.Reduced.Gentzen
