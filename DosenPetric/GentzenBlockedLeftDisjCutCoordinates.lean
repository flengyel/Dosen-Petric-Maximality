module

public import DosenPetric.GentzenTerminalExchangeFold

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.BlockedLeftDisj
universe u
variable {P : Type u}

theorem child_cut_denote {F D I R : List (NormalForm P)} {A C : NormalForm P}
    (h : G P I (C::R)) (f : G P (C::(F++[A])) D) :
    comp (tensor .conj (ofTerm (append .conj F I).toTerm) (id A))
      (comp (TerminalFold.into (F++I) A)
        (ofTerm ((terminalExchange F A I).inverse.left (G.cut h f)).denote)) =
      comp (terminalCross (ante F) (ante I) A)
        (comp (splice (ofTerm h.denote) (childArrow f)) (ofTerm (append .disj D R).toTerm)) := by
  rw [ExchangeScript.left_denote,cut_splice]
  rw [← Laws.assoc (tensor .conj (ofTerm (append .conj F I).toTerm) (id A)),
    ← Laws.assoc (comp (tensor .conj (ofTerm (append .conj F I).toTerm) (id A))
      (TerminalFold.into (F++I) A)),
    ← Laws.assoc (comp (comp (tensor .conj (ofTerm (append .conj F I).toTerm) (id A))
      (TerminalFold.into (F++I) A)) ((terminalExchange F A I).inverse.arrow .conj))]
  have he := terminal_child_into F A I
  simp only [← Laws.assoc] at he
  erw [he]
  simp only [Laws.assoc]
  rw [← Laws.assoc (tensor .conj (TerminalFold.into F A) (id (ante I))),← Splice.context]
  rfl

theorem sourceConj_split {F H I : List (NormalForm P)} {A B D E : NormalForm P}
    (f : Hom (.conj (ante (F++I)) A) D) (g : Hom (.conj (ante (H++I)) B) E) :
    comp (ofTerm (Rules.sourceConj (ante (F++I)) (ante (H++I)) A B)) (tensor .disj f g) =
      comp (tensor .conj
        (tensor .conj (ofTerm (append .conj F I).invTerm) (ofTerm (append .conj H I).invTerm))
        (id (.disj A B)))
        (comp (ofTerm (Rules.sourceConj (.conj (ante F) (ante I)) (.conj (ante H) (ante I)) A B))
          (tensor .disj
            (comp (tensor .conj (ofTerm (append .conj F I).toTerm) (id A)) f)
            (comp (tensor .conj (ofTerm (append .conj H I).toTerm) (id B)) g))) := by
  have hn := sourceConj_nat (ofTerm (append .conj F I).invTerm)
    (ofTerm (append .conj H I).invTerm) (id A) (id B)
  rw [Laws.tensor_id] at hn
  have he := congrArg (fun v => comp v (tensor .disj
    (comp (tensor .conj (ofTerm (append .conj F I).toTerm) (id A)) f)
    (comp (tensor .conj (ofTerm (append .conj H I).toTerm) (id B)) g))) hn
  have hf : comp (tensor .conj (ofTerm (append .conj F I).invTerm) (id A))
      (comp (tensor .conj (ofTerm (append .conj F I).toTerm) (id A)) f) = f := by
    rw [← Laws.assoc,Laws.tensor_comp,(append .conj F I).inv_to,Laws.id_comp,Laws.tensor_id,Laws.id_comp]
  have hg : comp (tensor .conj (ofTerm (append .conj H I).invTerm) (id B))
      (comp (tensor .conj (ofTerm (append .conj H I).toTerm) (id B)) g) = g := by
    rw [← Laws.assoc,Laws.tensor_comp,(append .conj H I).inv_to,Laws.id_comp,Laws.tensor_id,Laws.id_comp]
  simp only [Laws.assoc] at he
  rw [Laws.tensor_comp,hf,hg] at he
  exact he

theorem parallelInput_square {Y F H : List (NormalForm P)}
    (p : Route Y F) (q : Route Y H) (Q : NormalForm P) (I : List (NormalForm P)) :
    comp ((terminalExchange Y Q I).arrow .conj)
      (comp (ofTerm ((BlockedMix.inputRoute q p I).parallel (Route.identity [Q])).product)
        (comp (TerminalFold.sourceInput (F++I) (H++I) Q)
          (tensor .conj
            (tensor .conj (ofTerm (append .conj F I).invTerm) (ofTerm (append .conj H I).invTerm))
            (id Q)))) =
      comp (ofTerm (append .conj (Y++[Q]) I).invTerm)
        (comp (tensor .conj (TerminalFold.out Y Q) (id (ante I)))
          (sharedInput (p.sideArrow .conj) (q.sideArrow .conj) Q)) := by
  unfold TerminalFold.sourceInput
  simp only [Laws.assoc]
  rw [← Laws.assoc (ofTerm ((BlockedMix.inputRoute q p I).parallel (Route.identity [Q])).product),
    TerminalFold.parallel_out]
  simp only [Laws.assoc,Laws.tensor_comp,Laws.comp_id]
  have hr := BlockedMix.input_square_conj q p I
  erw [hr]
  have ht {V W Z : NormalForm P} (a : Hom V W) (b : Hom W Z) :
      tensor .conj (comp a b) (id Q) = comp (tensor .conj a (id Q)) (tensor .conj b (id Q)) := by
    rw [Laws.tensor_comp,Laws.comp_id]
  rw [ht]
  rw [← Laws.assoc ((terminalExchange Y Q I).arrow .conj),
    ← Laws.assoc (comp ((terminalExchange Y Q I).arrow .conj) (TerminalFold.out (Y++I) Q)),
    Laws.assoc ((terminalExchange Y Q I).arrow .conj),terminalExchange_out]
  simp only [sharedInput,Laws.assoc]

end DosenPetric.Reduced.Gentzen.BlockedLeftDisj
