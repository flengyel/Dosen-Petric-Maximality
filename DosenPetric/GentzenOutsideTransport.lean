module

public import DosenPetric.GentzenSiblingTransport

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

/-- Distinct proof occurrences whose paths first diverge at two actual siblings. -/
inductive SpineApart : {Γ Δ I J U V : List (NormalForm P)}→
    {root : G P Γ Δ}→{g : G P I J}→{v : G P U V}→
    ProofSpine root g→ProofSpine root v→Prop where
  | fork {Γ Δ I J I' J' U V U' V'} {root : G P Γ Δ}
      {f : G P I J} {k : G P I' J'} {g : G P U V} {v : G P U' V'}
      (p : Premise root f) (q : Premise root k) (a : ProofSpine f g) (b : ProofSpine k v)
      (hn : p.branch≠q.branch) : SpineApart (.down p a) (.down q b)
  | down {Γ Δ I J U V U' V'} {root : G P Γ Δ} {f : G P I J}
      {g : G P U V} {v : G P U' V'} (p : Premise root f)
      (a : ProofSpine f g) (b : ProofSpine f v) (hab : SpineApart a b) :
      SpineApart (.down p a) (.down p b)

namespace ProofAddress
variable {Γ Δ I J : List (NormalForm P)} {root : G P Γ Δ} {f : G P I J}
theorem ascend_one (p : Premise root f) (s : SequentSide)
    {C : NormalForm P} (x : Place s I J C) :
    (ProofAddress.root.down p).ascend s x=p.parent s x := by
  change (p.parent s x).bind (fun y=>some y)=_
  cases p.parent s x <;> rfl
end ProofAddress
namespace ProofSpine
variable {Γ Δ I J U V : List (NormalForm P)}
variable {root : G P Γ Δ} {f : G P I J} {g : G P U V}

theorem replace_down (p : Premise root f) (a : ProofSpine f g) (h : G P U V) :
    (ProofSpine.down p a).toAddress.replace h=p.rebuild (a.toAddress.replace h) := by
  rw [toAddress,ProofAddress.replace_append]
  rfl

theorem ascend_down (p : Premise root f) (a : ProofSpine f g) (s : SequentSide)
    {C : NormalForm P} (x : Place s U V C) :
    (ProofSpine.down p a).toAddress.ascend s x=(a.toAddress.ascend s x).bind (p.parent s) := by
  rw [toAddress,ProofAddress.ascend_append]
  exact congrArg (Option.bind (a.toAddress.ascend s x))
    (funext (fun y=>ProofAddress.ascend_one p s y))
end ProofSpine

namespace SpineApart
variable {Γ Δ I J U V : List (NormalForm P)}
variable {root : G P Γ Δ} {g : G P I J} {v : G P U V}
variable {a : ProofSpine root g} {b : ProofSpine root v}

/-- Every outside proof occurrence survives with its proof value, path and all
whole-formula ancestry maps unchanged. No denotation or rank premise is used. -/
theorem outside (hab : SpineApart a b) (h : G P I J) :
    ∃ c : ProofAddress (a.toAddress.replace h) v,
      c.path=b.path ∧ ∀ (s : SequentSide) {C : NormalForm P} (x : Place s U V C),
        c.ascend s x=b.toAddress.ascend s x := by
  induction hab with
  | @fork Γ Δ I J I' J' U V U' V' root f k g v p q a b hn=>
    let j:=a.toAddress.replace h
    let r:=p.sibling q hn j
    have he:=ProofSpine.replace_down p a h
    rw [he]
    refine ⟨(ProofAddress.root.down r).append b.toAddress,?_,?_⟩
    · rw [ProofAddress.append_path,ProofSpine.toAddress_path]
      change [r.branch]++b.path=q.branch::b.path
      rw [Premise.sibling_branch]
      rfl
    · intro s C x
      rw [ProofAddress.ascend_append,ProofSpine.ascend_down]
      rw [show (ProofAddress.root.down r).ascend s=r.parent s from
        funext (fun y=>ProofAddress.ascend_one r s y)]
      change (b.toAddress.ascend s x).bind (r.parent s)=(b.toAddress.ascend s x).bind (q.parent s)
      cases hx : b.toAddress.ascend s x with
      | none=>rfl
      | some y=>exact Premise.sibling_parent p q hn j s y
  | @down Γ Δ I J U V U' V' root f g v p a b hab ih=>
    obtain ⟨c,hc,ha⟩:=ih h
    rw [ProofSpine.replace_down]
    refine ⟨(ProofAddress.root.down (p.inserted (a.toAddress.replace h))).append c,?_,?_⟩
    · rw [ProofAddress.append_path,hc]
      change [(p.inserted _).branch]++b.path=p.branch::b.path
      rw [Premise.inserted_branch]
      rfl
    · intro s C x
      rw [ProofAddress.ascend_append,ha,ProofSpine.ascend_down]
      rw [show (ProofAddress.root.down (p.inserted (a.toAddress.replace h))).ascend s=
        (p.inserted (a.toAddress.replace h)).parent s from
        funext (fun y=>ProofAddress.ascend_one _ s y)]
      change (b.toAddress.ascend s x).bind ((p.inserted _).parent s)=_
      cases hx : b.toAddress.ascend s x with
      | none=>rfl
      | some y=>exact Premise.inserted_parent p _ s y
end SpineApart
end DosenPetric.Reduced.Gentzen

namespace DosenPetric.Reduced.Gentzen.ProofAddress
universe u
variable {P : Type u} {Γ Δ I J U V : List (NormalForm P)}
variable {root : G P Γ Δ} {g : G P I J} {v : G P U V}

/-- Address form of the outside-site transport theorem. The premise identifies
actual diverging branches; it does not compare proof values or formula labels. -/
theorem outside_transport (a : ProofAddress root g) (b : ProofAddress root v)
    (hab : SpineApart a.spine b.spine) (h : G P I J) :
    ∃ c : ProofAddress (a.replace h) v,
      c.path=b.path ∧ ∀ (s : SequentSide) {C : NormalForm P} (x : Place s U V C),
        c.ascend s x=b.ascend s x := by
  have he:=hab.outside h
  rw [a.spine_toAddress] at he
  simpa only [spine_toAddress,spine_path] using he
end DosenPetric.Reduced.Gentzen.ProofAddress
