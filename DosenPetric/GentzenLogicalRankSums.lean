module

public import DosenPetric.GentzenLogicalEmbeddings

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.GapLogical.Data
universe u
variable {P : Type u} {o : Op} (d : Data P o)

theorem sum_survivors {α β : Type u} (xs : List α) (p : α → Option β) (r : α → Nat) (s : β → Nat)
    (hs : ∀ a, a ∈ xs → ∃ b, p a = some b)
    (hr : ∀ a, a ∈ xs → ∀ b, p a = some b → s b = 1+r a) :
    ((xs.flatMap (fun a => (p a).toList)).map s).sum = (xs.map r).sum + xs.length := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    obtain ⟨b,hb⟩ := hs a List.mem_cons_self
    have ht := ih (fun a ha => hs a (List.mem_cons_of_mem _ ha))
      (fun a ha b hp => hr a (List.mem_cons_of_mem _ ha) b hp)
    simp only [List.flatMap_cons,hb,Option.toList_some,List.singleton_append,List.map_cons,List.sum_cons,List.length_cons]
    rw [hr a List.mem_cons_self b hb,ht]
    omega

theorem selected_sum (r : At d.U0 d.C → Nat) (s : At d.U1 d.C → Nat)
    (hr : ∀ a, a ∈ d.selected0 → ∀ b, d.uParent a = some b → s b = 1+r a) :
    (d.selected1.map s).sum = (d.selected0.map r).sum + d.gs0.length := by
  rw [← d.selected_transport,← d.selected0_length]
  exact sum_survivors d.selected0 d.uParent r s d.selected0_survives hr

end DosenPetric.Reduced.Gentzen.GapLogical.Data
