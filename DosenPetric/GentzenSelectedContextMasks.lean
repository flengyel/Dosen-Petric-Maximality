module

public import DosenPetric.GentzenTerminalProofTransports
public import DosenPetric.GentzenSourceSelectionBridge

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace SelectionMask
variable {C : NormalForm P} {Γ Θ : List (NormalForm P)}

def selectedContext (g : SelectionMask C Γ) (t : SelectionMask C Θ) : SelectionMask C (Γ++C::Θ) :=
  g.append (.pick t)

def selectedTerminal (g : SelectionMask C Γ) (t : SelectionMask C Θ) :
    SelectionMask C ((Γ++Θ)++[C]) := (g.append t).append (.pick .nil)

theorem selectedContext_erased (g : SelectionMask C Γ) (t : SelectionMask C Θ) :
    (selectedContext g t).erased=g.erased++t.erased := by
  rw [selectedContext,append_erased]

theorem selectedTerminal_erased (g : SelectionMask C Γ) (t : SelectionMask C Θ) :
    (selectedTerminal g t).erased=g.erased++t.erased := by
  rw [selectedTerminal,append_erased,append_erased]
  exact List.append_nil _

theorem selectedContext_count (g : SelectionMask C Γ) (t : SelectionMask C Θ) :
    (selectedContext g t).count=g.count+t.count+1 := by
  rw [selectedContext,append_count]
  change g.count+(t.count+1)=_
  omega

theorem selectedTerminal_count (g : SelectionMask C Γ) (t : SelectionMask C Θ) :
    (selectedTerminal g t).count=g.count+t.count+1 := by
  rw [selectedTerminal,append_count,append_count]
  rfl

theorem selected_terminal_index (g : SelectionMask C Γ) (t : SelectionMask C Θ)
    {A : NormalForm P} (a : At (Γ++C::Θ) A) :
    ((selectedContext g t).canonical.get a).index=
      ((selectedTerminal g t).canonical.get ((Route.moveEnd Γ [C] Θ).get a)).index := by
  cases At.cases_append Γ (C::Θ) a with
  | inl h=>
    obtain ⟨a,rfl⟩:=h
    have he:=Route.moveEnd_before Γ [C] Θ a
    simp only [List.singleton_append] at he
    rw [he,canonical_index,canonical_index]
    simp only [selectedContext,selectedTerminal,append_picked_before,append_offset_before]
  | inr h=>
    obtain ⟨a,rfl⟩:=h
    cases a with
    | here=>
      have he:=Route.moveEnd_middle Γ [C] Θ (.here C [])
      simp only [At.before,List.nil_append] at he
      rw [he,canonical_index,canonical_index]
      simp only [selectedContext,selectedTerminal,append_picked_shift,picked,ite_true]
    | there a=>
      have he:=Route.moveEnd_tail Γ [C] Θ a
      change (Route.moveEnd Γ [C] Θ).get (At.shift Γ a.there)=(At.shift Γ a).before [C] at he
      rw [he,canonical_index,canonical_index]
      simp only [selectedContext,selectedTerminal,append_picked_shift,append_picked_before,
        append_offset_shift,append_offset_before,picked,offset]
end SelectionMask
namespace ContractionBound

theorem weaken {s : SequentSide} {C : NormalForm P} {k n : Nat}
    {Γ Δ : List (NormalForm P)} {g : G P Γ Δ} {E : Place s Γ Δ C→Prop}
    (h : ContractionBound s C k g E) (hn : k≤n) : ContractionBound s C n g E := by
  induction h with
  | bounded he=>exact .bounded (fun a ha=>Nat.lt_of_lt_of_le (he a ha) hn)
  | step reject children ih=>exact .step reject (fun j=>ih j)
end ContractionBound
end DosenPetric.Reduced.Gentzen
