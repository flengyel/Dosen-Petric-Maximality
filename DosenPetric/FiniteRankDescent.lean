module

public import Init

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.FiniteRank

/-- Finite multisets are represented by lists; order ignores list order but
retains multiplicity. At some rank its count drops, and every higher count agrees. -/
def Descent (new old : List Nat) : Prop :=
  ∃ r, new.count r < old.count r ∧ ∀ k, r < k → new.count k = old.count k

def Vector : Nat → Type
  | 0 => Unit
  | n+1 => Nat × Vector n

def Less : (n : Nat) → Vector n → Vector n → Prop
  | 0 => fun _ _ => False
  | n+1 => Prod.Lex Nat.lt (Less n)

theorem less_wf : ∀ n, WellFounded (Less n)
  | 0 => ⟨fun x => .intro x (fun _ h => False.elim h)⟩
  | n+1 => (Prod.lex Nat.lt_wfRel ⟨Less n,less_wf n⟩).wf

/-- Counts from rank N-1 down to rank zero, for a fixed support bound N. -/
def counts : (n : Nat) → List Nat → Vector n
  | 0,_ => ()
  | n+1,xs => (xs.count n,counts n xs)

theorem counts_lt {new old : List Nat} (N r : Nat) (hr : r < N)
    (hc : new.count r < old.count r)
    (hh : ∀ k, r < k → new.count k = old.count k) :
    Less N (counts N new) (counts N old) := by
  induction N with
  | zero => omega
  | succ N ih =>
    by_cases he : r = N
    · subst r
      exact Prod.Lex.left _ _ hc
    · have hn : r < N := by omega
      have hk := hh N hn
      change Prod.Lex Nat.lt (Less N) (new.count N,counts N new) (old.count N,counts N old)
      rw [hk]
      exact Prod.Lex.right _ (ih hn)

def Bounded (N : Nat) (xs : List Nat) : Prop := ∀ k ∈ xs, k < N

theorem pivot_lt {new old : List Nat} {N r : Nat}
    (hb : Bounded N old) (hc : new.count r < old.count r) : r < N :=
  hb r (List.count_pos_iff.mp (by omega))

theorem bounded_step {new old : List Nat} {N : Nat}
    (hs : Descent new old) (hb : Bounded N old) : Bounded N new := by
  obtain ⟨r,hc,hh⟩ := hs
  have hr := pivot_lt hb hc
  intro k hk
  by_cases hkr : k ≤ r
  · omega
  · have he := hh k (by omega)
    have hp : 0 < old.count k := by rw [← he]; exact List.count_pos_iff.mpr hk
    exact hb k (List.count_pos_iff.mp hp)

theorem counts_descent {new old : List Nat} {N : Nat}
    (hs : Descent new old) (hb : Bounded N old) :
    Less N (counts N new) (counts N old) := by
  obtain ⟨r,hc,hh⟩ := hs
  exact counts_lt N r (pivot_lt hb hc) hc hh

theorem bounded_accessible (N : Nat) (old : List Nat) (hb : Bounded N old) :
    Acc Descent old := by
  have ha := (less_wf N).apply (counts N old)
  generalize he : counts N old = v at ha
  induction ha generalizing old with
  | intro v lower ih =>
    constructor
    intro new hs
    apply ih (counts N new)
    · rw [← he]
      exact counts_descent hs hb
    · exact bounded_step hs hb
    · rfl

def supportBound : List Nat → Nat
  | [] => 0
  | k::ks => max (k+1) (supportBound ks)

theorem support_bounded (xs : List Nat) : Bounded (supportBound xs) xs := by
  induction xs with
  | nil => intro k hk; cases hk
  | cons a xs ih =>
    intro k hk
    cases hk with
    | head => exact Nat.lt_of_lt_of_le (Nat.lt_succ_self a) (Nat.le_max_left _ _)
    | tail _ hk => exact Nat.lt_of_lt_of_le (ih k hk) (Nat.le_max_right _ _)

/-- Strict replacement of finite natural rank multisets is well founded. -/
theorem descent_wf : WellFounded Descent :=
  ⟨fun xs => bounded_accessible (supportBound xs) xs (support_bounded xs)⟩

/-- Replacing one entry by any finite collection of smaller entries decreases
the multiset order, including when the inserted collection is empty. -/
theorem of_replacement {old new outside inserted : List Nat} {r : Nat}
    (ho : old.Perm (r::outside)) (hn : new.Perm (inserted++outside))
    (hi : ∀ k ∈ inserted, k < r) : Descent new old := by
  have hz : ∀ k, r ≤ k → inserted.count k = 0 := by
    intro k hk
    apply List.count_eq_zero_of_not_mem
    intro hm
    have hh := hi k hm
    omega
  refine ⟨r,?_,?_⟩
  · rw [ho.count_eq r,hn.count_eq r,List.count_append,hz r (Nat.le_refl r),
      List.count_cons_self,Nat.zero_add]
    omega
  · intro k hk
    rw [ho.count_eq k,hn.count_eq k,List.count_append,hz k (by omega),
      List.count_cons_of_ne (by omega),Nat.zero_add]

end DosenPetric.FiniteRank
