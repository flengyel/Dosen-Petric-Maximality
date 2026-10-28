module

public import DosenPetric.GentzenBlockedReplacement

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

namespace Premise
theorem rebuild_sourceArity {Γ Δ U V : List (NormalForm P)}
    {k : G P Γ Δ} {w : G P U V} (p : Premise k w) (h : G P U V)
    (s : SequentSide) {C : NormalForm P} (x : Place s Γ Δ C) :
    (p.rebuild h).sourceArity s x = k.sourceArity s x := by
  cases p <;> cases s <;> rfl
end Premise

namespace ProofSpine
variable {Γ Δ U V I J : List (NormalForm P)}
variable {k : G P Γ Δ} {w : G P U V} {v : G P I J}

/-- Two actual typed addresses are comparable by a typed suffix or diverge
at two distinct immediate branches. Equal subproof values do not merge paths. -/
theorem compare (a : ProofSpine k w) (b : ProofSpine k v) :
    (∃ c : ProofAddress w v, a.toAddress.append c = b.toAddress) ∨
    (∃ c : ProofAddress v w, b.toAddress.append c = a.toAddress) ∨
    SpineApart a b := by
  induction a with
  | root => exact .inl ⟨b.toAddress,ProofAddress.root_append _⟩
  | @down Γ Δ U V I J k f w p a ih =>
    cases b with
    | root => exact .inr (.inl ⟨(ProofSpine.down p a).toAddress,ProofAddress.root_append _⟩)
    | @down _ _ U' V' I' J' _ f' v q b =>
      by_cases hp : p.branch = q.branch
      · have he : (⟨U,V,f,p⟩ : Branch k) = ⟨U',V',f',q⟩ := Branch.eq_of_branch _ _ hp
        cases he
        rcases ih b with ⟨c,hc⟩ | ⟨c,hc⟩ | hc
        · refine .inl ⟨c,?_⟩
          simpa only [toAddress,ProofAddress.append_assoc] using
            (congrArg (fun d => (ProofAddress.root.down p).append d) hc)
        · refine .inr (.inl ⟨c,?_⟩)
          simpa only [toAddress,ProofAddress.append_assoc] using
            (congrArg (fun d => (ProofAddress.root.down p).append d) hc)
        · exact .inr (.inr (.down p a b hc))
      · exact .inr (.inr (.fork p q a b hp))

theorem replace_sourceArity (a : ProofSpine k w) (hp : a.path ≠ [])
    (h : G P U V) (s : SequentSide) {C : NormalForm P} (x : Place s Γ Δ C) :
    (a.toAddress.replace h).sourceArity s x = k.sourceArity s x := by
  cases a with
  | root => exact False.elim (hp rfl)
  | down p b => rw [replace_down]; exact p.rebuild_sourceArity _ s x

/-- A path prefix factors through an actual dependent address. -/
theorem suffix_of_prefix (a : ProofSpine k w) (b : ProofSpine k v)
    (hp : ∃ xs, a.path++xs = b.path) :
    ∃ c : ProofAddress w v, a.toAddress.append c = b.toAddress := by
  induction a with
  | root => exact ⟨b.toAddress,ProofAddress.root_append _⟩
  | @down Γ Δ U V I J k f w p a ih =>
    cases b with
    | root =>
      obtain ⟨xs,hxs⟩ := hp
      cases hxs
    | @down _ _ U' V' I' J' _ f' v q b =>
      obtain ⟨xs,hxs⟩ := hp
      have hpq : p.branch = q.branch := (List.cons.inj hxs).1
      have he : (⟨U,V,f,p⟩ : Branch k) = ⟨U',V',f',q⟩ := Branch.eq_of_branch _ _ hpq
      cases he
      obtain ⟨c,hc⟩ := ih b ⟨xs,(List.cons.inj hxs).2⟩
      refine ⟨c,?_⟩
      simpa only [toAddress,ProofAddress.append_assoc] using
        (congrArg (fun d => (ProofAddress.root.down p).append d) hc)

/-- Every raw prefix of an existing path has a typed occurrence and suffix. -/
theorem split_prefix (a : ProofSpine k w) (xs : List Nat)
    (hp : ∃ ys, xs++ys = a.path) :
    ∃ (I J : List (NormalForm P)) (v : G P I J)
      (b : ProofAddress k v) (c : ProofAddress v w), b.append c = a.toAddress ∧ b.path = xs := by
  induction a generalizing xs with
  | root =>
    obtain ⟨ys,hy⟩ := hp
    have hx : xs = [] := List.eq_nil_of_append_eq_nil hy |>.1
    subst xs
    exact ⟨_,_,_,.root,.root,rfl,rfl⟩
  | @down Γ Δ U V I J k f w p a ih =>
    cases xs with
    | nil => exact ⟨_,_,k,.root,(ProofSpine.down p a).toAddress,
        ProofAddress.root_append _,rfl⟩
    | cons i xs =>
      obtain ⟨ys,hy⟩ := hp
      have hi : i = p.branch := (List.cons.inj hy).1
      subst i
      obtain ⟨I',J',v,b,c,hc,hb⟩ := ih xs ⟨ys,(List.cons.inj hy).2⟩
      refine ⟨I',J',v,(ProofAddress.root.down p).append b,c,?_,?_⟩
      · rw [ProofAddress.append_assoc,hc]; rfl
      · rw [ProofAddress.append_path,hb]; rfl
end ProofSpine

namespace ProofAddress
variable {Γ Δ U V I J : List (NormalForm P)}
variable {k : G P Γ Δ} {w : G P U V} {v : G P I J}

theorem compare (a : ProofAddress k w) (b : ProofAddress k v) :
    (∃ c : ProofAddress w v, a.append c = b) ∨
    (∃ c : ProofAddress v w, b.append c = a) ∨ SpineApart a.spine b.spine := by
  simpa only [spine_toAddress] using a.spine.compare b.spine

theorem suffix_of_prefix (a : ProofAddress k w) (b : ProofAddress k v)
    (hp : ∃ xs, a.path++xs = b.path) :
    ∃ c : ProofAddress w v, a.append c = b := by
  simpa only [spine_toAddress] using a.spine.suffix_of_prefix b.spine
    (by simpa only [spine_path] using hp)

theorem split_prefix (a : ProofAddress k w) (xs : List Nat)
    (hp : ∃ ys, xs++ys = a.path) :
    ∃ (I J : List (NormalForm P)) (v : G P I J)
      (b : ProofAddress k v) (c : ProofAddress v w), b.append c = a ∧ b.path = xs := by
  simpa only [spine_toAddress] using a.spine.split_prefix xs
    (by simpa only [spine_path] using hp)

/-- Proper replacement leaves the containing rule and its lower positions intact. -/
theorem replace_lower_iff (a : ProofAddress k w) (hp : a.path ≠ [])
    (h : G P U V) (s : SequentSide) {C : NormalForm P} (x : Place s Γ Δ C) :
    (a.replace h).LowerContraction s x ↔ k.LowerContraction s x := by
  rw [G.lowerContraction_iff_arity,G.lowerContraction_iff_arity]
  have he := a.spine.replace_sourceArity
    (by simpa only [spine_path] using hp) h s x
  simpa only [spine_toAddress] using (congrArg (fun n => 2 ≤ n) he).to_iff
end ProofAddress

end DosenPetric.Reduced.Gentzen
