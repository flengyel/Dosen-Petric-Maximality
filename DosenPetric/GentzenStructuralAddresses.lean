module

public import DosenPetric.GentzenStructuralCutReplacement
public import DosenPetric.GentzenStructuralProgramRanks

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace StructuralProgram

/-- The actual address of the original proof under an antecedent structural program. -/
noncomputable def leftAddress {F U Δ : List (NormalForm P)} (p : StructuralProgram P F U)
    (f : G P U Δ) : ProofAddress (p.left f) f := by
  induction p with
  | identity => exact .root
  | seq p q ih ih' => exact (ih (q.left f)).append (ih' f)
  | exchange F X Y U => exact .down .root (.exchangeL F X Y U Δ f)
  | thin F U E => exact .down .root (.thinL F U Δ E f)
  | contract E gs U hn => exact .down .root (.contractL E gs U Δ hn f)
  | reindex hF hU p ih => cases hF; cases hU; exact ih f

/-- The actual address of the original proof under a succedent structural program. -/
noncomputable def rightAddress {F U Γ : List (NormalForm P)} (p : StructuralProgram P F U)
    (f : G P Γ U) : ProofAddress (p.right f) f := by
  induction p with
  | identity => exact .root
  | seq p q ih ih' => exact (ih (q.right f)).append (ih' f)
  | exchange F X Y U => exact .down .root (.exchangeR Γ F X Y U f)
  | thin F U E => exact .down .root (.thinR Γ F U E f)
  | contract E gs U hn => exact .down .root (.contractR Γ E gs U hn f)
  | reindex hF hU p ih => cases hF; cases hU; exact ih f

theorem leftAddress_seq {F U K Δ : List (NormalForm P)} (p : StructuralProgram P F U)
    (q : StructuralProgram P U K) (f : G P K Δ) :
    (p.seq q).leftAddress f = (p.leftAddress (q.left f)).append (q.leftAddress f) := rfl

theorem rightAddress_seq {F U K Γ : List (NormalForm P)} (p : StructuralProgram P F U)
    (q : StructuralProgram P U K) (f : G P Γ K) :
    (p.seq q).rightAddress f = (p.rightAddress (q.right f)).append (q.rightAddress f) := rfl

theorem leftAddress_ascend {F U Δ : List (NormalForm P)} (p : StructuralProgram P F U)
    (f : G P U Δ) {C : NormalForm P} (y : At U C) :
    (p.leftAddress f).ascend .left y = some (p.get y) := by
  induction p with
  | identity => rfl
  | seq p q ih ih' => rw [leftAddress_seq, ProofAddress.ascend_append, ih', Option.bind_some, ih]; rfl
  | exchange => rfl
  | thin => rfl
  | contract => rfl
  | reindex hF hU p ih => cases hF; cases hU; exact ih f y

theorem rightAddress_ascend {F U Γ : List (NormalForm P)} (p : StructuralProgram P F U)
    (f : G P Γ U) {C : NormalForm P} (y : At U C) :
    (p.rightAddress f).ascend .right y = some (p.get y) := by
  induction p with
  | identity => rfl
  | seq p q ih ih' => rw [rightAddress_seq, ProofAddress.ascend_append, ih', Option.bind_some, ih]; rfl
  | exchange => rfl
  | thin => rfl
  | contract => rfl
  | reindex hF hU p ih => cases hF; cases hU; exact ih f y

/-- Antecedent structural programs preserve every opposite-side whole-formula tag. -/
theorem leftAddress_opposite {F U Δ : List (NormalForm P)} (p : StructuralProgram P F U)
    (f : G P U Δ) {C : NormalForm P} (y : At Δ C) :
    (p.leftAddress f).ascend .right y = some y := by
  induction p with
  | identity => rfl
  | seq p q ih ih' => rw [leftAddress_seq, ProofAddress.ascend_append, ih', Option.bind_some, ih]
  | exchange => rfl
  | thin => rfl
  | contract => rfl
  | reindex hF hU p ih => cases hF; cases hU; exact ih f

/-- Succedent structural programs preserve every opposite-side whole-formula tag. -/
theorem rightAddress_opposite {F U Γ : List (NormalForm P)} (p : StructuralProgram P F U)
    (f : G P Γ U) {C : NormalForm P} (y : At Γ C) :
    (p.rightAddress f).ascend .left y = some y := by
  induction p with
  | identity => rfl
  | seq p q ih ih' => rw [rightAddress_seq, ProofAddress.ascend_append, ih', Option.bind_some, ih]
  | exchange => rfl
  | thin => rfl
  | contract => rfl
  | reindex hF hU p ih => cases hF; cases hU; exact ih f

theorem leftAddress_length {F U Δ : List (NormalForm P)} (p : StructuralProgram P F U)
    (f : G P U Δ) : (p.leftAddress f).path.length = p.steps := by
  induction p with
  | identity => rfl
  | seq p q ih ih' => rw [leftAddress_seq, ProofAddress.append_path, List.length_append, ih, ih']; rfl
  | exchange => rfl
  | thin => rfl
  | contract => rfl
  | reindex hF hU p ih => cases hF; cases hU; exact ih f

theorem rightAddress_length {F U Γ : List (NormalForm P)} (p : StructuralProgram P F U)
    (f : G P Γ U) : (p.rightAddress f).path.length = p.steps := by
  induction p with
  | identity => rfl
  | seq p q ih ih' => rw [rightAddress_seq, ProofAddress.append_path, List.length_append, ih, ih']; rfl
  | exchange => rfl
  | thin => rfl
  | contract => rfl
  | reindex hF hU p ih => cases hF; cases hU; exact ih f

end StructuralProgram
end DosenPetric.Reduced.Gentzen
