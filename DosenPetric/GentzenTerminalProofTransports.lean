module

public import DosenPetric.GentzenLogicalTerminalNaturality

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace At

def reinsert (Γ Θ M : List (NormalForm P)) {A : NormalForm P} (a : At (Γ++Θ) A) :
    At (Γ++(M++Θ)) A :=
  match At.splitAppend Γ Θ a with
  | .inl b=>b.before (M++Θ)
  | .inr b=>At.shift Γ (At.shift M b)

theorem reinsert_before (Γ Θ M : List (NormalForm P)) {A : NormalForm P} (a : At Γ A) :
    reinsert Γ Θ M (a.before Θ)=a.before (M++Θ) := by
  rw [reinsert,At.splitAppend_before]

theorem reinsert_shift (Γ Θ M : List (NormalForm P)) {A : NormalForm P} (a : At Θ A) :
    reinsert Γ Θ M (At.shift Γ a)=At.shift Γ (At.shift M a) := by
  rw [reinsert,At.splitAppend_shift]

theorem moveEnd_reinsert (Γ Θ M : List (NormalForm P)) {A : NormalForm P} (a : At (Γ++Θ) A) :
    (Route.moveEnd Γ M Θ).get (reinsert Γ Θ M a)=a.before M := by
  cases At.cases_append Γ Θ a with
  | inl h=>obtain ⟨a,rfl⟩:=h;rw [reinsert_before,Route.moveEnd_before]
  | inr h=>obtain ⟨a,rfl⟩:=h;rw [reinsert_shift,Route.moveEnd_tail]
end At
namespace G

def moveEndL (Γ M Θ Δ : List (NormalForm P)) (f : G P (Γ++(M++Θ)) Δ) :
    G P ((Γ++Θ)++M) Δ :=
  UnaryCast.exchangeL Γ M Θ []
    ((List.append_nil ((Γ++M)++Θ)).trans (List.append_assoc Γ M Θ))
    (List.append_nil ((Γ++Θ)++M)) Δ f

def moveEndR (Δ Γ M Θ : List (NormalForm P)) (f : G P Δ (Γ++(M++Θ))) :
    G P Δ ((Γ++Θ)++M) :=
  UnaryCast.exchangeR Γ M Θ []
    ((List.append_nil ((Γ++M)++Θ)).trans (List.append_assoc Γ M Θ))
    (List.append_nil ((Γ++Θ)++M)) Δ f

theorem moveEndL_denote (Γ M Θ Δ : List (NormalForm P)) (f : G P (Γ++(M++Θ)) Δ) :
    ofTerm (moveEndL Γ M Θ Δ f).denote=
      comp (ofTerm (Route.moveEnd Γ M Θ).product) (ofTerm f.denote) :=
  UnaryCast.exchangeL_denote ..

theorem moveEndR_denote (Δ Γ M Θ : List (NormalForm P)) (f : G P Δ (Γ++(M++Θ))) :
    ofTerm (moveEndR Δ Γ M Θ f).denote=
      comp (ofTerm f.denote) (ofTerm (Route.moveEnd Γ M Θ).coproduct) :=
  UnaryCast.exchangeR_denote ..

theorem moveEndL_rank (Γ M Θ Δ : List (NormalForm P)) (f : G P (Γ++(M++Θ)) Δ)
    {A : NormalForm P} (a : At (Γ++(M++Θ)) A) :
    (moveEndL Γ M Θ Δ f).rho .left ((Route.moveEnd Γ M Θ).get a)=1+f.rho .left a :=
  UnaryCast.exchangeL_embedded ..

theorem moveEndR_rank (Δ Γ M Θ : List (NormalForm P)) (f : G P Δ (Γ++(M++Θ)))
    {A : NormalForm P} (a : At (Γ++(M++Θ)) A) :
    (moveEndR Δ Γ M Θ f).rho .right ((Route.moveEnd Γ M Θ).get a)=1+f.rho .right a :=
  UnaryCast.exchangeR_embedded ..

theorem moveEndL_count (Γ M Θ Δ : List (NormalForm P)) (f : G P (Γ++(M++Θ)) Δ) :
    (moveEndL Γ M Θ Δ f).cutCount=f.cutCount := by
  simp only [moveEndL,UnaryCast.exchangeL,G.count_reindex,G.cutCount]

theorem moveEndR_count (Δ Γ M Θ : List (NormalForm P)) (f : G P Δ (Γ++(M++Θ))) :
    (moveEndR Δ Γ M Θ f).cutCount=f.cutCount := by
  simp only [moveEndR,UnaryCast.exchangeR,G.count_reindex,G.cutCount]
end G
end DosenPetric.Reduced.Gentzen
