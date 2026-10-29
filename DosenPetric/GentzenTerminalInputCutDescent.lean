module

public import DosenPetric.GentzenTerminalCutDescent

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace UnaryCast

theorem exchangeL_right_cut_descent {F U Δ I J : List (NormalForm P)}
    (Γ X Y Θ : List (NormalForm P)) (hF : Γ++X++Y++Θ=F) (hU : Γ++Y++X++Θ=U)
    (f : G P F Δ) {C : NormalForm P} (a : At F C) (h : G P I J) (z : At J C)
    (hc : PositionalCut.Clean h z (exchangeL Γ X Y Θ hF hU Δ f)
      (((Route.exchange Γ X Y Θ).cast hU hF).get a)) :
    PositionalCut.Clean h z f a ∧
      PositionalCut.rank h z f a < PositionalCut.rank h z (exchangeL Γ X Y Θ hF hU Δ f)
        (((Route.exchange Γ X Y Θ).cast hU hF).get a) := by
  cases hU
  cases hF
  let b : Upper (G.exchangeL Γ X Y Θ Δ f) .left C :=
    ⟨⟨_,_,f,Premise.exchangeL Γ X Y Θ Δ f⟩,a⟩
  have hb : (G.exchangeL Γ X Y Θ Δ f).IsPredecessor .left
      ((Route.exchange Γ X Y Θ).get a) b := by
    change some (a.swapBlocks Γ X Y Θ) = some ((Route.exchange Γ X Y Θ).get a)
    rw [Route.exchange_get]
  exact ⟨PositionalCut.clean_right_predecessor hc b hb,
    PositionalCut.rank_right_predecessor h z _ _ b hb⟩

end UnaryCast
namespace BlockedSource

theorem disjLLast_right_first_descent {F U Δ Λ I J : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P (F++[A]) Δ) (g : G P (U++[B]) Λ) (a : At F C) (h : G P I J) (z : At J C)
    (hc : PositionalCut.Clean h z (disjLLast f g) ((a.before U).before [.disj A B])) :
    PositionalCut.Clean h z f (a.before [A]) ∧
      PositionalCut.rank h z f (a.before [A]) <
        PositionalCut.rank h z (disjLLast f g) ((a.before U).before [.disj A B]) := by
  rw [disjLLast_eq] at hc ⊢
  have ht := UnaryCast.exchangeL_right_cut_descent (U := (F++U)++[.disj A B]) [] [.disj A B] (F++U) []
    (by simp only [List.nil_append,List.singleton_append,List.append_nil])
    (by simp only [List.nil_append,List.append_nil])
    (G.disjL (headL A f) (headL B g)) (At.there (B:=.disj A B) (a.before U)) h z
  change PositionalCut.Clean h z (tailL (.disj A B) (G.disjL (headL A f) (headL B g)))
      ((Route.toTail (F++U) (.disj A B)).get (.there (a.before U))) →
    PositionalCut.Clean h z (G.disjL (headL A f) (headL B g)) (.there (a.before U)) ∧
    PositionalCut.rank h z (G.disjL (headL A f) (headL B g)) (.there (a.before U)) <
      PositionalCut.rank h z (tailL (.disj A B) (G.disjL (headL A f) (headL B g)))
        ((Route.toTail (F++U) (.disj A B)).get (.there (a.before U))) at ht
  rw [Route.toTail_there] at ht
  have hm := PositionalCut.disjL_right_first_descent (headL A f) (headL B g) h z a (ht hc).1
  have hf := UnaryCast.exchangeL_right_cut_descent (U := A::F) [] F [A] []
    (by simp only [List.nil_append,List.append_nil])
    (by simp only [List.nil_append,List.singleton_append,List.append_nil]) f (a.before [A]) h z
  change PositionalCut.Clean h z (headL A f) ((Route.toHead F A).get (a.before [A])) →
    PositionalCut.Clean h z f (a.before [A]) ∧
    PositionalCut.rank h z f (a.before [A]) <
      PositionalCut.rank h z (headL A f) ((Route.toHead F A).get (a.before [A])) at hf
  rw [Route.toHead_before] at hf
  exact ⟨(hf hm.1).1,Nat.lt_trans (hf hm.1).2 (Nat.lt_trans hm.2 (ht hc).2)⟩

theorem disjLLast_right_second_descent {F U Δ Λ I J : List (NormalForm P)} {A B C : NormalForm P}
    (f : G P (F++[A]) Δ) (g : G P (U++[B]) Λ) (a : At U C) (h : G P I J) (z : At J C)
    (hc : PositionalCut.Clean h z (disjLLast f g) ((At.shift F a).before [.disj A B])) :
    PositionalCut.Clean h z g (a.before [B]) ∧
      PositionalCut.rank h z g (a.before [B]) <
        PositionalCut.rank h z (disjLLast f g) ((At.shift F a).before [.disj A B]) := by
  rw [disjLLast_eq] at hc ⊢
  have ht := UnaryCast.exchangeL_right_cut_descent (U := (F++U)++[.disj A B]) [] [.disj A B] (F++U) []
    (by simp only [List.nil_append,List.singleton_append,List.append_nil])
    (by simp only [List.nil_append,List.append_nil])
    (G.disjL (headL A f) (headL B g)) (At.there (B:=.disj A B) (At.shift F a)) h z
  change PositionalCut.Clean h z (tailL (.disj A B) (G.disjL (headL A f) (headL B g)))
      ((Route.toTail (F++U) (.disj A B)).get (.there (At.shift F a))) →
    PositionalCut.Clean h z (G.disjL (headL A f) (headL B g)) (.there (At.shift F a)) ∧
    PositionalCut.rank h z (G.disjL (headL A f) (headL B g)) (.there (At.shift F a)) <
      PositionalCut.rank h z (tailL (.disj A B) (G.disjL (headL A f) (headL B g)))
        ((Route.toTail (F++U) (.disj A B)).get (.there (At.shift F a))) at ht
  rw [Route.toTail_there] at ht
  have hm := PositionalCut.disjL_right_second_descent (headL A f) (headL B g) h z a (ht hc).1
  have hg := UnaryCast.exchangeL_right_cut_descent (U := B::U) [] U [B] []
    (by simp only [List.nil_append,List.append_nil])
    (by simp only [List.nil_append,List.singleton_append,List.append_nil]) g (a.before [B]) h z
  change PositionalCut.Clean h z (headL B g) ((Route.toHead U B).get (a.before [B])) →
    PositionalCut.Clean h z g (a.before [B]) ∧
    PositionalCut.rank h z g (a.before [B]) <
      PositionalCut.rank h z (headL B g) ((Route.toHead U B).get (a.before [B])) at hg
  rw [Route.toHead_before] at hg
  exact ⟨(hg hm.1).1,Nat.lt_trans (hg hm.1).2 (Nat.lt_trans hm.2 (ht hc).2)⟩

end BlockedSource
end DosenPetric.Reduced.Gentzen
