module

public import DosenPetric.GentzenEntrySeparation

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.EntryFrame
universe u
variable {P : Type u} {C : NormalForm P}
theorem there_index {Ξ : List (NormalForm P)} (B : NormalForm P) (a : At Ξ C) :
    (a.there : At (B::Ξ) C).index = a.index+1 := rfl
attribute [local simp] At.index_shift At.index_before there_index swapBlocks_index

def UniqueOn (F : Nat → Prop) (lo hi : Nat) : Prop :=
  ∀ i j, F i → F j → lo ≤ i → i < hi → lo ≤ j → j < hi → i = j

theorem before_unique (F : Nat → Prop) {Γ Θ : List (NormalForm P)}
    (h : UniqueOn F 0 Γ.length) (y z : At Γ C)
    (hy : F (y.before Θ).index) (hz : F (z.before Θ).index) : y.before Θ = z.before Θ := by
  apply At.index_injective
  apply h _ _ hy hz
  · omega
  · rw [At.index_before]; exact y.index_lt
  · omega
  · rw [At.index_before]; exact z.index_lt

theorem shift_unique (F : Nat → Prop) {Γ Θ : List (NormalForm P)}
    (h : UniqueOn F Γ.length (Γ.length+Θ.length)) (y z : At Θ C)
    (hy : F (At.shift Γ y).index) (hz : F (At.shift Γ z).index) : At.shift Γ y = At.shift Γ z := by
  apply At.index_injective
  apply h _ _ hy hz
  all_goals rw [At.index_shift]
  all_goals first | omega | (have hh := y.index_lt; omega) | (have hh := z.index_lt; omega)

theorem before_wrapped_unique (F : Nat → Prop) (D : NormalForm P) {Γ Θ : List (NormalForm P)}
    (h : UniqueOn F 1 (1+Γ.length)) (y z : At Γ C)
    (hy : F ((y.before Θ).there : At (D::(Γ++Θ)) C).index)
    (hz : F ((z.before Θ).there : At (D::(Γ++Θ)) C).index) :
    (y.before Θ).there = (z.before Θ).there (B := D) := by
  apply At.index_injective
  apply h _ _ hy hz
  all_goals rw [there_index,At.index_before]
  all_goals first | omega | (have hh := y.index_lt; omega) | (have hh := z.index_lt; omega)

theorem shift_wrapped_unique (F : Nat → Prop) (D : NormalForm P) {Γ Θ : List (NormalForm P)}
    (h : UniqueOn F (1+Γ.length) (1+Γ.length+Θ.length)) (y z : At Θ C)
    (hy : F ((At.shift Γ y).there : At (D::(Γ++Θ)) C).index)
    (hz : F ((At.shift Γ z).there : At (D::(Γ++Θ)) C).index) :
    (At.shift Γ y).there = (At.shift Γ z).there (B := D) := by
  apply At.index_injective
  apply h _ _ hy hz
  all_goals rw [there_index,At.index_shift]
  all_goals first | omega | (have hh := y.index_lt; omega) | (have hh := z.index_lt; omega)

theorem mix {Γ Θ Δ Λ : List (NormalForm P)} (f : G P Γ Δ) (g : G P Θ Λ)
    (s : SequentSide) (F : Nat → Prop)
    (hl : UniqueOn F 0 (s.context Θ Λ).length)
    (hr : UniqueOn F (s.context Θ Λ).length
      ((s.context Θ Λ).length+(s.context Γ Δ).length)) :
    EntryFrame s C (G.mix f g) (fun x => F x.index) := by
  apply immediate
  · intro x h
    have ha := (G.lowerContraction_iff_arity _ _ _).mp h
    simp only [G.sourceArity] at ha
    first | omega | (split at ha <;> omega)
  · intro j x x' y z hx hx' hy hz
    have hb := G.branches_complete j
    simp only [G.branches,List.mem_cons,List.not_mem_nil,or_false] at hb
    rcases hb with rfl | rfl <;> cases s
    all_goals dsimp only [Place,SequentSide.context] at *
    all_goals
      have hxy := Option.some.inj hy
      have hxz := Option.some.inj hz
      subst x
      subst x'
      first
      | exact before_unique F hl y z hx hx'
      | exact shift_unique F hr y z hx hx'
      | exact before_wrapped_unique F _ hl y z hx hx'
      | exact shift_wrapped_unique F _ hr y z hx hx'

theorem conj_left {Γ Θ Δ Λ : List (NormalForm P)} {A B : NormalForm P}
    (f : G P Γ (A::Δ)) (g : G P Θ (B::Λ)) (F : Nat → Prop)
    (hl : UniqueOn F 0 Γ.length) (hr : UniqueOn F Γ.length (Γ.length+Θ.length)) :
    EntryFrame .left C (G.conjR f g) (fun x => F x.index) := by
  apply immediate
  · intro x h
    have ha := (G.lowerContraction_iff_arity _ _ _).mp h
    simp only [G.sourceArity] at ha
    first | omega | (split at ha <;> omega)
  · intro j x x' y z hx hx' hy hz
    have hb := G.branches_complete j
    simp only [G.branches,List.mem_cons,List.not_mem_nil,or_false] at hb
    rcases hb with rfl | rfl
    all_goals dsimp only [Place,SequentSide.context] at *
    all_goals
      have hxy := Option.some.inj hy
      have hxz := Option.some.inj hz
      subst x
      subst x'
      first
      | exact before_unique F hl y z hx hx'
      | exact shift_unique F hr y z hx hx'
      | exact before_wrapped_unique F _ hl y z hx hx'
      | exact shift_wrapped_unique F _ hr y z hx hx'

theorem disj_right {Γ Θ Δ Λ : List (NormalForm P)} {A B : NormalForm P}
    (f : G P (A::Γ) Δ) (g : G P (B::Θ) Λ) (F : Nat → Prop)
    (hl : UniqueOn F 0 Δ.length) (hr : UniqueOn F Δ.length (Δ.length+Λ.length)) :
    EntryFrame .right C (G.disjL f g) (fun x => F x.index) := by
  apply immediate
  · intro x h
    have ha := (G.lowerContraction_iff_arity _ _ _).mp h
    simp only [G.sourceArity] at ha
    first | omega | (split at ha <;> omega)
  · intro j x x' y z hx hx' hy hz
    have hb := G.branches_complete j
    simp only [G.branches,List.mem_cons,List.not_mem_nil,or_false] at hb
    rcases hb with rfl | rfl
    all_goals dsimp only [Place,SequentSide.context] at *
    all_goals
      have hxy := Option.some.inj hy
      have hxz := Option.some.inj hz
      subst x
      subst x'
      first
      | exact before_unique F hl y z hx hx'
      | exact shift_unique F hr y z hx hx'
      | exact before_wrapped_unique F _ hl y z hx hx'
      | exact shift_wrapped_unique F _ hr y z hx hx'

theorem disj_left {Γ Θ Δ Λ : List (NormalForm P)} {A B : NormalForm P}
    (f : G P (A::Γ) Δ) (g : G P (B::Θ) Λ) (F : Nat → Prop)
    (hl : UniqueOn F 1 (1+Γ.length))
    (hr : UniqueOn F (1+Γ.length) (1+Γ.length+Θ.length)) :
    EntryFrame .left C (G.disjL f g) (fun x => F x.index) := by
  apply immediate
  · intro x h
    have ha := (G.lowerContraction_iff_arity _ _ _).mp h
    simp only [G.sourceArity] at ha
    first | omega | (split at ha <;> omega)
  · intro j x x' y z hx hx' hy hz
    have hb := G.branches_complete j
    simp only [G.branches,List.mem_cons,List.not_mem_nil,or_false] at hb
    rcases hb with rfl | rfl
    all_goals dsimp only [Place,SequentSide.context] at *
    all_goals cases y with
    | here => cases hy
    | there y => cases z with
      | here => cases hz
      | there z =>
        have hxy := Option.some.inj hy
        have hxz := Option.some.inj hz
        subst x
        subst x'
        first
        | exact before_unique F hl y z hx hx'
        | exact shift_unique F hr y z hx hx'
        | exact before_wrapped_unique F _ hl y z hx hx'
        | exact shift_wrapped_unique F _ hr y z hx hx'

theorem conj_right {Γ Θ Δ Λ : List (NormalForm P)} {A B : NormalForm P}
    (f : G P Γ (A::Δ)) (g : G P Θ (B::Λ)) (F : Nat → Prop)
    (hl : UniqueOn F 1 (1+Δ.length))
    (hr : UniqueOn F (1+Δ.length) (1+Δ.length+Λ.length)) :
    EntryFrame .right C (G.conjR f g) (fun x => F x.index) := by
  apply immediate
  · intro x h
    have ha := (G.lowerContraction_iff_arity _ _ _).mp h
    simp only [G.sourceArity] at ha
    first | omega | (split at ha <;> omega)
  · intro j x x' y z hx hx' hy hz
    have hb := G.branches_complete j
    simp only [G.branches,List.mem_cons,List.not_mem_nil,or_false] at hb
    rcases hb with rfl | rfl
    all_goals dsimp only [Place,SequentSide.context] at *
    all_goals cases y with
    | here => cases hy
    | there y => cases z with
      | here => cases hz
      | there z =>
        have hxy := Option.some.inj hy
        have hxz := Option.some.inj hz
        subst x
        subst x'
        first
        | exact before_unique F hl y z hx hx'
        | exact shift_unique F hr y z hx hx'
        | exact before_wrapped_unique F _ hl y z hx hx'
        | exact shift_wrapped_unique F _ hr y z hx hx'

theorem exchange_left {Γ X Y Θ Δ : List (NormalForm P)}
    (f : G P (Γ++X++Y++Θ) Δ) (s : SequentSide) (F : Nat → Prop)
    (hf : EntryFrame s C f (fun x => F (match s with
      | .left => exchangeIndex Γ.length X.length Y.length x.index
      | .right => x.index))) :
    EntryFrame s C (G.exchangeL Γ X Y Θ Δ f) (fun x => F x.index) := by
  apply step
  · intro x h
    have hh := (G.lowerContraction_iff_arity _ _ _).mp h
    change 2 ≤ 1 at hh
    omega
  · intro j
    have hb := G.branches_complete j
    simp only [G.branches,List.mem_singleton] at hb
    cases hb
    apply hf.mono
    rintro y ⟨x,hx,hp⟩
    cases s with
    | left =>
      have he := Option.some.inj hp
      subst x
      change F (exchangeIndex Γ.length X.length Y.length y.index)
      exact (swapBlocks_index Γ X Y Θ y) ▸ hx
    | right =>
      have he := Option.some.inj hp
      subst x
      exact hx

def UniqueExcept (F : Nat → Prop) (k : Nat) : Prop :=
  ∀ i j, F i → F j → i ≠ k → j ≠ k → i = j

theorem unary_logical {Γ Δ : List (NormalForm P)} (g : G P Γ Δ)
    (s : SequentSide) (F : Nat → Prop) (k : Nat)
    (hn : ∀ x : Place s Γ Δ C, ¬ g.LowerContraction s x)
    (hk : ∀ x : Place s Γ Δ C, x.index = k → g.Leaf s x)
    (hf : UniqueExcept F k) : EntryFrame s C g (fun x => F x.index) := by
  apply immediate hn
  intro j x x' y z hx hx' hy hz
  have hnx : x.index ≠ k := fun he => (g.leaf_iff_no_predecessor s x).mp (hk x he) ⟨j,y⟩ hy
  have hnx' : x'.index ≠ k := fun he => (g.leaf_iff_no_predecessor s x').mp (hk x' he) ⟨j,z⟩ hz
  cases s <;> exact At.index_injective x x' (hf _ _ hx hx' hnx hnx')

theorem conjunction {Γ Θ Δ : List (NormalForm P)} {A B : NormalForm P}
    (f : G P (Γ++A::B::Θ) Δ) (F : Nat → Prop) (hf : UniqueExcept F Γ.length) :
    EntryFrame .left C (G.conjL Γ Θ Δ A B f) (fun x => F x.index) := by
  apply unary_logical _ .left F Γ.length
  · intro x h
    have hh := (G.lowerContraction_iff_arity _ _ _).mp h
    simp only [G.sourceArity] at hh
    split at hh <;> omega
  · intro x hx
    simp only [G.Leaf,G.sourceArity,hx,ite_true]
  · exact hf

theorem disjunction {Γ Δ Λ : List (NormalForm P)} {A B : NormalForm P}
    (f : G P Γ (Δ++A::B::Λ)) (F : Nat → Prop) (hf : UniqueExcept F Δ.length) :
    EntryFrame .right C (G.disjR Γ Δ Λ A B f) (fun x => F x.index) := by
  apply unary_logical _ .right F Δ.length
  · intro x h
    have hh := (G.lowerContraction_iff_arity _ _ _).mp h
    simp only [G.sourceArity] at hh
    split at hh <;> omega
  · intro x hx
    simp only [G.Leaf,G.sourceArity,hx,ite_true]
  · exact hf

end DosenPetric.Reduced.Gentzen.EntryFrame
