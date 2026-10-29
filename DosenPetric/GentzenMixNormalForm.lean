module

public import DosenPetric.GentzenPureNormalFormRules

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace HasPureNormalForm

theorem identity (l : Literal P) : HasPureNormalForm (ofTerm (G.identity l).denote) := by
  let e : PureEdge (ante [.lit l]) (succ [.lit l]) :=
    ⟨l,.left .top (.here l),.left .bot (.here l)⟩
  have he : e.arrow = ofTerm (G.identity l).denote := by
    change comp (comp (fst (.lit l) .top) (id (.lit l)))
      (comp (id (.lit l)) (inl (.lit l) .bot)) =
      comp (rightOut .conj (.lit l)) (comp (id (.lit l)) (rightIn .disj (.lit l)))
    rw [Laws.comp_id,Laws.id_comp,Laws.id_comp,Laws.fst_top,Laws.inl_bot]
  exact congr he (edge e)

theorem zero_leaf (l : Literal P) : HasPureNormalForm (ofTerm (G.zero l).denote) := by
  exact congr (zeroOf_pre (rightOut .conj (.lit l)) (rightIn .disj (.lit l))).symm
    (zero (comp (rightOut .conj (.lit l)) (rightIn .disj (.lit l))))

theorem top_leaf : HasPureNormalForm (ofTerm (G.topI (P:=P)).denote) :=
  congr (fromTop_unique _ _) (zero (ofTerm (G.topI (P:=P)).denote))

theorem bot_leaf : HasPureNormalForm (ofTerm (G.botE (P:=P)).denote) :=
  congr (toBot_unique _ _) (zero (ofTerm (G.botE (P:=P)).denote))

end HasPureNormalForm
namespace G

/-- Actual finite atomic normalization of every proof in the mix fragment. -/
theorem mix_normal_form {Γ Δ : List (NormalForm P)} (g : G P Γ Δ) (hg : g.MixOnly) :
    HasPureNormalForm (ofTerm g.denote) := by
  induction g with
  | identity l => exact HasPureNormalForm.identity l
  | zero l => exact HasPureNormalForm.zero_leaf l
  | topI => exact HasPureNormalForm.top_leaf
  | botE => exact HasPureNormalForm.bot_leaf
  | exchangeL F X Y U Δ f ih =>
    exact HasPureNormalForm.program_left (.exchange F X Y U) f (ih hg)
  | exchangeR Γ F X Y U f ih =>
    exact HasPureNormalForm.program_right (.exchange F X Y U) f (ih hg)
  | thinL F U Δ A f ih => exact HasPureNormalForm.program_left (.thin F U A) f (ih hg)
  | thinR Γ F U A f ih => exact HasPureNormalForm.program_right (.thin F U A) f (ih hg)
  | contractL A gs U Δ hn f ih =>
    exact HasPureNormalForm.program_left (.contract A gs U hn) f (ih hg)
  | contractR Γ A gs U hn f ih =>
    exact HasPureNormalForm.program_right (.contract A gs U hn) f (ih hg)
  | conjL F U Δ A B f ih => exact HasPureNormalForm.conjL A B f (ih hg)
  | disjR Γ F U A B f ih => exact HasPureNormalForm.disjR A B f (ih hg)
  | conjR => exact False.elim hg
  | disjL => exact False.elim hg
  | mix f g ih ih' => exact HasPureNormalForm.mix f g (ih hg.1) (ih' hg.2)
  | cut => exact False.elim hg

theorem mix_faithful {Γ Δ : List (NormalForm P)} (f g : G P Γ Δ)
    (hf : f.MixOnly) (hg : g.MixOnly) (h : f.relation = g.relation) :
    ofTerm f.denote = ofTerm g.denote :=
  HasPureNormalForm.faithful (f.mix_normal_form hf) (g.mix_normal_form hg) h

/-- Pure cut-free proofs have equal arrows whenever their full tagged relations agree. -/
theorem pure_cutFree_faithful {Γ Δ : List (NormalForm P)} (f g : G P Γ Δ)
    (hf : f.CutFree) (hg : g.CutFree)
    (hΓ : PureContext .conj Γ) (hΔ : PureContext .disj Δ) (h : f.relation = g.relation) :
    ofTerm f.denote = ofTerm g.denote :=
  f.mix_faithful g (f.mixOnly_of_pure hf hΓ hΔ) (g.mixOnly_of_pure hg hΓ hΔ) h

end G
end DosenPetric.Reduced.Gentzen
