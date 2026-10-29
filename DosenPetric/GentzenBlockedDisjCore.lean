module

public import DosenPetric.GentzenMirrorBlockedConjCore

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.BlockedDisj
universe u
variable {P : Type u}

/-- The source's terminal-input comparison, with the two selected outputs shared. -/
def rightParent {Γ Θ Δ Λ Y A B C : NormalForm P} (p : Hom Δ Y) (q : Hom Λ Y)
    (f : Hom (.conj Γ A) (.disj Δ C)) (g : Hom (.conj Θ B) (.disj Λ C)) :
    Hom (.conj (.conj Γ Θ) (.disj A B)) (.disj Y C) :=
  comp (ofTerm (Rules.sourceConj Γ Θ A B))
    (comp (tensor .disj f g)
      (copair (tensor .disj p (id C)) (tensor .disj q (id C))))

/-- Both original child cuts use the same right premise. -/
theorem right_shared_splice {Γ Θ Δ Λ Y A B C T Z : NormalForm P}
    (p : Hom Δ Y) (q : Hom Λ Y)
    (f : Hom (.conj Γ A) (.disj Δ C)) (g : Hom (.conj Θ B) (.disj Λ C))
    (h : Hom (.conj T C) Z) :
    comp (assocL .conj T (.conj Γ Θ) (.disj A B))
      (splice (comp (rightParent p q f g) (swap .disj Y C))
        (comp (swap .conj C T) h)) =
      comp (tensor .conj (BlockedMix.rightSharedInput T Γ Θ) (id (.disj A B)))
        (comp (ofTerm (Rules.sourceConj (.conj T Γ) (.conj T Θ) A B))
          (comp (tensor .disj
            (comp (assocL .conj T Γ A)
              (splice (comp f (swap .disj Δ C)) (comp (swap .conj C T) h)))
            (comp (assocL .conj T Θ B)
              (splice (comp g (swap .disj Λ C)) (comp (swap .conj C T) h))))
            (BlockedMix.rightSharedOutput q p))) := by
  obtain ⟨a,rfl⟩ : ∃ a' : NormalForm P, mirror a' = A := ⟨mirror A,mirror_involutive A⟩
  obtain ⟨b,rfl⟩ : ∃ b' : NormalForm P, mirror b' = B := ⟨mirror B,mirror_involutive B⟩
  obtain ⟨c,rfl⟩ : ∃ c' : NormalForm P, mirror c' = C := ⟨mirror C,mirror_involutive C⟩
  obtain ⟨γ,rfl⟩ : ∃ γ' : NormalForm P, mirror γ' = Γ := ⟨mirror Γ,mirror_involutive Γ⟩
  obtain ⟨θ,rfl⟩ : ∃ θ' : NormalForm P, mirror θ' = Θ := ⟨mirror Θ,mirror_involutive Θ⟩
  obtain ⟨δ,rfl⟩ : ∃ δ' : NormalForm P, mirror δ' = Δ := ⟨mirror Δ,mirror_involutive Δ⟩
  obtain ⟨lmb,rfl⟩ : ∃ lmb' : NormalForm P, mirror lmb' = Λ := ⟨mirror Λ,mirror_involutive Λ⟩
  obtain ⟨y,rfl⟩ : ∃ y' : NormalForm P, mirror y' = Y := ⟨mirror Y,mirror_involutive Y⟩
  obtain ⟨t,rfl⟩ : ∃ t' : NormalForm P, mirror t' = T := ⟨mirror T,mirror_involutive T⟩
  obtain ⟨z,rfl⟩ : ∃ z' : NormalForm P, mirror z' = Z := ⟨mirror Z,mirror_involutive Z⟩
  have he := @MirrorCalculus.BlockedConj.shared_splice P c y lmb δ b a θ γ z t q p g f h
  simp only [MirrorCalculus.BlockedConj.sharedParent,MirrorInterpretation.splice_native,
    MirrorInterpretation.mixed_source] at he
  dsimp only [MirrorCalculus.comp,MirrorCalculus.tensor,MirrorCalculus.pair,
    MirrorCalculus.copair,MirrorCalculus.id,MirrorCalculus.inl,MirrorCalculus.inr,
    MirrorCalculus.assocL,MirrorCalculus.BlockedMix.sharedInput,
    MirrorCalculus.BlockedMix.sharedOutput,mirror] at he
  simpa only [rightParent,BlockedMix.rightSharedInput,BlockedMix.rightSharedOutput,BlockedMix.tensor_copair,Laws.assoc] using he

/-- The same common-output comparison with both selected outputs at the head. -/
def headRightParent {Γ Θ Δ Λ Y A B C : NormalForm P} (p : Hom Δ Y) (q : Hom Λ Y)
    (f : Hom (.conj Γ A) (.disj C Δ)) (g : Hom (.conj Θ B) (.disj C Λ)) :
    Hom (.conj (.conj Γ Θ) (.disj A B)) (.disj C Y) :=
  comp (ofTerm (Rules.sourceConj Γ Θ A B))
    (comp (tensor .disj f g)
      (copair (tensor .disj (id C) p) (tensor .disj (id C) q)))

theorem parent_tail_head {Γ Θ Δ Λ Y A B C : NormalForm P} (p : Hom Δ Y) (q : Hom Λ Y)
    (f : Hom (.conj Γ A) (.disj C Δ)) (g : Hom (.conj Θ B) (.disj C Λ)) :
    comp (rightParent p q (comp f (swap .disj C Δ)) (comp g (swap .disj C Λ)))
      (swap .disj Y C) = headRightParent p q f g := by
  have hp {D : NormalForm P} (v : Hom D Y) :
      comp (swap .disj C D) (comp (tensor .disj v (id C)) (swap .disj Y C)) =
        tensor .disj (id C) v := by
    rw [← Laws.assoc,Laws.swap_nat,Laws.assoc,Laws.swap_swap,Laws.comp_id]
  simp only [rightParent,headRightParent,BlockedMix.tensor_copair,BlockedMix.copair_post,Laws.assoc]
  rw [hp,hp]

/-- Native head-selected form of the terminal disjunction comparison. -/
theorem head_right_shared_splice {Γ Θ Δ Λ Y A B C T Z : NormalForm P}
    (p : Hom Δ Y) (q : Hom Λ Y)
    (f : Hom (.conj Γ A) (.disj C Δ)) (g : Hom (.conj Θ B) (.disj C Λ))
    (h : Hom (.conj C T) Z) :
    comp (assocL .conj T (.conj Γ Θ) (.disj A B))
      (splice (headRightParent p q f g) h) =
      comp (tensor .conj (BlockedMix.rightSharedInput T Γ Θ) (id (.disj A B)))
        (comp (ofTerm (Rules.sourceConj (.conj T Γ) (.conj T Θ) A B))
          (comp (tensor .disj
            (comp (assocL .conj T Γ A) (splice f h))
            (comp (assocL .conj T Θ B) (splice g h)))
            (BlockedMix.rightSharedOutput q p))) := by
  have he := right_shared_splice p q (comp f (swap .disj C Δ))
    (comp g (swap .disj C Λ)) (comp (swap .conj T C) h)
  rw [parent_tail_head] at he
  simp only [← Laws.assoc,Laws.swap_swap,Laws.id_comp] at he
  simpa only [Laws.assoc,Laws.swap_swap,Laws.comp_id] using he

end DosenPetric.Reduced.Gentzen.BlockedDisj
