module

public import DosenPetric.FormulaRenaming

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.ProfileComposition
open FiniteBlocks

/-- The outer profile and the profiles of all inserted patterns. Zero-sized
families are allowed exactly when the displayed functions exist. -/
structure Data (m k : Nat) where
  outer : Fin m → Fin k
  n : Fin k → Nat
  l : Fin k → Nat
  inner : ∀ i, Fin (n i) → Fin (l i)

namespace Data
variable {m k : Nat} (S : Data m k)
abbrev Domain := Block (fun r => S.n (S.outer r))
abbrev Codomain := Block S.l

def a (r : Fin m) (t : Fin (S.n (S.outer r))) : S.Domain := ⟨r,t⟩
def b (i : Fin k) (s : Fin (S.l i)) : S.Codomain := ⟨i,s⟩
def gamma (x : S.Domain) : S.Codomain := ⟨S.outer x.1,S.inner (S.outer x.1) x.2⟩

theorem a_injective (r : Fin m) {t t' : Fin (S.n (S.outer r))}
    (h : S.a r t = S.a r t') : t = t' := by cases h; rfl

theorem b_injective (i : Fin k) {s s' : Fin (S.l i)} (h : S.b i s = S.b i s') : s = s' := by
  cases h; rfl

theorem fibre_square (r : Fin m) (t : Fin (S.n (S.outer r))) :
    S.gamma (S.a r t) = S.b (S.outer r) (S.inner (S.outer r) t) := rfl

theorem gamma_unique (g : S.Domain → S.Codomain)
    (h : ∀ r t, g (S.a r t) = S.b (S.outer r) (S.inner (S.outer r) t)) : g = S.gamma := by
  funext ⟨r,t⟩
  exact h r t

theorem profile_square (x : S.Domain) : (S.gamma x).1 = S.outer x.1 := rfl

theorem gamma_fibre (r : Fin m) (t : Fin (S.n (S.outer r))) (s : Fin (S.l (S.outer r))) :
    S.gamma ⟨r,t⟩ = S.b (S.outer r) s ↔ S.inner (S.outer r) t = s := by
  constructor
  · intro h
    exact eq_of_heq (Sigma.mk.inj h).2
  · intro h
    cases h
    rfl

/-- Change from dependent block coordinates to consecutive ordinal coordinates. -/
def delta (x : Fin (total (fun r => S.n (S.outer r)))) : Fin (total S.l) :=
  encode S.l (S.gamma (decode (fun r => S.n (S.outer r)) x))

theorem ordinal_square (x : S.Domain) :
    S.delta (encode (fun r => S.n (S.outer r)) x) = encode S.l (S.gamma x) := by
  simp only [delta,decode_encode]

theorem delta_unique (d : Fin (total (fun r => S.n (S.outer r))) → Fin (total S.l))
    (h : ∀ x : S.Domain, d (encode (fun r => S.n (S.outer r)) x) = encode S.l (S.gamma x)) :
    d = S.delta := by
  funext x
  rw [← encode_decode (fun r => S.n (S.outer r)) x,h,ordinal_square]

theorem coordinate_equation (r : Fin m) (t : Fin (S.n (S.outer r))) :
    (S.delta (encode (fun q => S.n (S.outer q)) ⟨r,t⟩)).val =
      prefixSum S.l (S.outer r) + (S.inner (S.outer r) t).val := by
  rw [ordinal_square,encode_value]
  rfl

theorem coordinate_oneBased (r : Fin m) (t : Fin (S.n (S.outer r))) :
    (oneBased (S.delta (encode (fun q => S.n (S.outer q)) ⟨r,t⟩))).val =
      prefixSum S.l (S.outer r) + (oneBased (S.inner (S.outer r) t)).val := by
  change (S.delta (encode (fun q => S.n (S.outer q)) ⟨r,t⟩)).val+1 =
    prefixSum S.l (S.outer r) + ((S.inner (S.outer r) t).val+1)
  rw [coordinate_equation,Nat.add_assoc]

/-- The book's block locator is unique even with intervening empty blocks. -/
theorem book_locator (x : Fin (total (fun r => S.n (S.outer r)))) :
    ∃ r : Fin m,
      (prefixSum (fun q => S.n (S.outer q)) r < (oneBased x).val ∧
       (oneBased x).val ≤ prefixSum (fun q => S.n (S.outer q)) r + S.n (S.outer r)) ∧
      ∀ i : Fin m,
        prefixSum (fun q => S.n (S.outer q)) i < (oneBased x).val →
        (oneBased x).val ≤ prefixSum (fun q => S.n (S.outer q)) i + S.n (S.outer i) → i = r := by
  refine ⟨(decode (fun q => S.n (S.outer q)) x).1,locator_oneBased _ x,?_⟩
  intro i lo hi
  apply (locator_unique (fun q => S.n (S.outer q)) x i ?_ ?_).symm
  all_goals simp only [oneBased] at lo hi; omega

/-- Section 2.5's generalized-composition formula, with the local coordinate
x-s_(r-1) and the output offset t_(mu(r)-1), in one-based coordinates. -/
theorem book_formula (x : Fin (total (fun r => S.n (S.outer r)))) :
    let z := decode (fun q => S.n (S.outer q)) x
    (oneBased z.2).val = (oneBased x).val-prefixSum (fun q => S.n (S.outer q)) z.1 ∧
    (oneBased (S.delta x)).val =
      prefixSum S.l (S.outer z.1) + (oneBased (S.inner (S.outer z.1) z.2)).val := by
  dsimp only
  have he := encode_value (fun q => S.n (S.outer q)) (decode (fun q => S.n (S.outer q)) x)
  rw [encode_decode] at he
  constructor
  · simp only [oneBased]
    omega
  · rw [← encode_decode (fun q => S.n (S.outer q)) x,coordinate_oneBased,decode_encode]

end Data
end DosenPetric.ProfileComposition
