module

public import DosenPetric.GentzenConjunction

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

theorem swap_snd (A B : NormalForm P) : comp (swap .conj A B) (snd B A) = fst A B := by
  rw [Laws.snd_swap, ← Laws.assoc, Laws.swap_swap, Laws.id_comp]

theorem two_top_out (A : NormalForm P) :
    comp (assocL .conj .top .top A)
      (comp (leftOut .conj (.conj .top A)) (leftOut .conj A)) = snd (.conj .top .top) A := by
  have h := congrArg (fun k => comp k (snd (NormalForm.top : NormalForm P) A))
    (Laws.fst_assoc (NormalForm.top : NormalForm P) .top A)
  simp only [Laws.assoc] at h
  rw [← Laws.snd_nat, ← Laws.snd_nat, Laws.comp_id] at h
  have hh := congrArg (fun k => comp (assocL .conj .top .top A) k) h
  rw [← Laws.assoc, Laws.assocL_R, Laws.id_comp] at hh
  have hu (X : NormalForm P) : snd .top X = leftOut .conj X := (conjDiagonal P).snd_unit X
  rw [hu, hu] at hh
  exact hh.symm

/-- Pure input part of disjunction-left, before its two premises. -/
def disjInput (A B : NormalForm P) :
    Term P (ante [.disj A B]) (.disj (ante [A]) (ante [B])) :=
  .comp (.tensor .conj (.id (.disj A B)) (.leftIn .conj .top))
    (.comp (.swap .conj (.disj A B) (.conj .top .top))
      (.comp (Rules.sourceConj .top .top A B)
        (.tensor .disj (.swap .conj .top A) (.swap .conj .top B))))

theorem disjInput_out (A B : NormalForm P) :
    comp (rightIn .conj (.disj A B))
      (comp (ofTerm (disjInput A B)) (tensor .disj (rightOut .conj A) (rightOut .conj B))) =
      id (.disj A B) := by
  change comp (rightIn .conj (.disj A B))
    (comp (comp (tensor .conj (id (.disj A B)) (leftIn .conj .top))
      (comp (swap .conj (.disj A B) (.conj .top .top))
        (comp (ofTerm (Rules.sourceConj .top .top A B))
          (tensor .disj (swap .conj .top A) (swap .conj .top B)))))
      (tensor .disj (rightOut .conj A) (rightOut .conj B))) = _
  simp only [Laws.assoc]
  change comp (rightIn .conj (.disj A B))
    (comp (tensor .conj (id (.disj A B)) (leftIn .conj .top))
      (comp (swap .conj (.disj A B) (.conj .top .top))
        (comp (comp (tensor .conj (id (.conj .top .top)) (swap .disj A B))
          (comp (assocL .conj .top .top (.disj B A))
            (comp (tensor .conj (id .top) (dist .top B A))
              (comp (tensor .conj (id .top) (swap .disj (.conj .top B) A))
                (dist .top A (.conj .top B))))))
          (comp (tensor .disj (swap .conj .top A) (swap .conj .top B))
            (tensor .disj (rightOut .conj A) (rightOut .conj B)))))) = _
  simp only [Laws.assoc]
  rw [Laws.tensor_comp, swap_unit_out, swap_unit_out]
  rw [dist_top (P := P) A (.conj .top B)]
  simp only [Laws.assoc]
  rw [Laws.tensor_comp, Laws.leftIn_Out, Laws.id_comp]
  rw [← Laws.assoc (tensor .conj (id .top) (swap .disj (.conj .top B) A)), ← Laws.leftOut_nat]
  simp only [Laws.assoc]
  rw [← Laws.assoc (tensor .conj (id .top) (dist .top B A)), ← Laws.leftOut_nat]
  simp only [Laws.assoc]
  rw [dist_top (P := P) B A]
  simp only [Laws.assoc]
  rw [← Laws.assoc (tensor .disj (leftIn .conj B) (id A)), ← Laws.swap_nat]
  simp only [Laws.assoc]
  rw [Laws.tensor_comp, Laws.id_comp, Laws.leftIn_Out, Laws.tensor_id, Laws.comp_id]
  rw [← Laws.assoc (leftOut .conj (.conj .top (.disj B A))),
    ← Laws.assoc (assocL .conj .top .top (.disj B A)), two_top_out]
  rw [← Laws.assoc (tensor .conj (id (.conj .top .top)) (swap .disj A B)), ← Laws.snd_nat]
  simp only [Laws.assoc]
  rw [Laws.swap_swap, Laws.comp_id, swap_snd, ← Laws.fst_nat, Laws.comp_id,
    Laws.fst_top, Laws.rightIn_Out]

theorem single_join (o : Op) (A B : NormalForm P) :
    comp (ofTerm (append o [A] [B]).toTerm)
      (comp (assocR o A B o.unit) (rightOut o (o.formula A B))) =
      tensor o (rightOut o A) (rightOut o B) := by
  apply cancel_left _ _ (tensor o (rightIn o A) (rightIn o B))
    (tensor o (rightOut o A) (rightOut o B))
    (by rw [Laws.tensor_comp, Laws.rightOut_In, Laws.rightOut_In, Laws.tensor_id])
  calc
    _ = id (o.formula A B) := by
      rw [← single_split]
      simp only [Laws.assoc]
      rw [← Laws.assoc (ofTerm (append o [A] [B]).invTerm), (append o [A] [B]).inv_to,
        Laws.id_comp, ← Laws.assoc (assocL o A B o.unit), Laws.assocL_R, Laws.id_comp,
        Laws.rightIn_Out]
    _ = _ := by
      rw [Laws.tensor_comp, Laws.rightIn_Out, Laws.rightIn_Out, Laws.tensor_id]

theorem append_insert (o : Op) (A B : NormalForm P) :
    comp (tensor o (rightIn o A) (rightIn o B)) (ofTerm (append o [A] [B]).toTerm) =
      tensor o (id A) (rightIn o B) := by
  rw [← single_split]
  simp only [Laws.assoc]
  rw [(append o [A] [B]).inv_to]
  change comp (rightIn o (o.formula A B))
    (comp (assocL o A B o.unit) (id (o.formula A (o.formula B o.unit)))) = _
  rw [Laws.comp_id, ← rightIn_tensor, Laws.assoc, Laws.assocR_L, Laws.comp_id]

theorem append_remove (o : Op) (A B : NormalForm P) :
    comp (ofTerm (append o [A] [B]).invTerm) (tensor o (rightOut o A) (rightOut o B)) =
      tensor o (id A) (rightOut o B) := by
  rw [← single_join]
  simp only [← Laws.assoc]
  rw [(append o [A] [B]).inv_to]
  change comp (comp (id (o.formula A (o.formula B o.unit))) (assocR o A B o.unit))
    (rightOut o (o.formula A B)) = _
  rw [Laws.id_comp, ← rightOut_tensor, ← Laws.assoc, Laws.assocR_L]
  exact Laws.id_comp _

/-- The pure disjunction-left comparison equals the two singleton unit insertions. -/
theorem disjInput_value (A B : NormalForm P) :
    comp (rightIn .conj (.disj A B)) (ofTerm (disjInput A B)) =
      tensor .disj (rightIn .conj A) (rightIn .conj B) := by
  apply cancel_right _ _ (tensor .disj (rightOut .conj A) (rightOut .conj B))
    (tensor .disj (rightIn .conj A) (rightIn .conj B))
    (by rw [Laws.tensor_comp, Laws.rightOut_In, Laws.rightOut_In, Laws.tensor_id])
  rw [Laws.assoc, disjInput_out, Laws.tensor_comp, Laws.rightIn_Out,
    Laws.rightIn_Out, Laws.tensor_id]

namespace G

def tensorDisj {A B C D : NormalForm P} (f : G P [A] [B]) (g : G P [C] [D]) :
    G P [.disj A C] [.disj B D] := .disjR _ [] [] B D (.disjL f g)

theorem tensorDisj_value {A B C D : NormalForm P} (f : G P [A] [B]) (g : G P [C] [D]) :
    decode (tensorDisj f g).denote = tensor .disj (decode f.denote) (decode g.denote) := by
  have hleft : ofTerm (Rules.disjLeft (Γ := []) (Θ := []) f.denote g.denote) =
      comp (ofTerm (disjInput A C))
        (comp (tensor .disj (ofTerm f.denote) (ofTerm g.denote))
          (ofTerm (append .disj [B] [D]).toTerm)) := by
    simp only [Rules.disjLeft, disjInput, ofTerm_comp, ofTerm_tensor, Laws.assoc]
    rfl
  change comp (rightIn .conj (.disj A C))
    (comp (comp (ofTerm (Rules.disjLeft (Γ := []) (Θ := []) f.denote g.denote))
      (assocR .disj B D .bot)) (rightOut .disj (.disj B D))) = _
  rw [hleft]
  simp only [Laws.assoc]
  rw [single_join, ← Laws.assoc (rightIn .conj (.disj A C)), disjInput_value,
    Laws.tensor_comp, Laws.tensor_comp]
  rfl

end G
end DosenPetric.Reduced.Gentzen
