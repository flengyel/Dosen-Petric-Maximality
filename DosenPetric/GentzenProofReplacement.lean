module

public import DosenPetric.GentzenPremiseReplacement

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.ProofAddress
universe u
variable {P : Type u} {Γ Δ Θ Λ Ξ Ω : List (NormalForm P)}
variable {root : G P Γ Δ} {g : G P Θ Λ} {k : G P Ξ Ω}

/-- Replace one proof occurrence, retaining all other branches. -/
def replace : {Θ Λ : List (NormalForm P)} → {g : G P Θ Λ} →
    ProofAddress root g → G P Θ Λ → G P Γ Δ
  | _,_,_,.root,h => h
  | _,_,_,.down a p,h => a.replace (p.rebuild h)

theorem replace_root (g h : G P Γ Δ) : (.root : ProofAddress g g).replace h = h := rfl

theorem replace_down (a : ProofAddress root g) (p : Premise g k) (h : G P Ξ Ω) :
    (a.down p).replace h = a.replace (p.rebuild h) := rfl

theorem replace_original (a : ProofAddress root g) : a.replace g = root := by
  induction a with
  | root => rfl
  | down a p ih => rw [replace_down,p.rebuild_original,ih]

/-- The inserted proof occurs at the original branch path. -/
def inserted : {Θ Λ : List (NormalForm P)} → {g : G P Θ Λ} →
    (a : ProofAddress root g) → (h : G P Θ Λ) → ProofAddress (a.replace h) h
  | _,_,_,.root,_ => .root
  | _,_,_,.down a p,h => (a.inserted (p.rebuild h)).down (p.inserted h)

theorem inserted_path (a : ProofAddress root g) (h : G P Θ Λ) :
    (a.inserted h).path = a.path := by
  induction a with
  | root => rfl
  | down a p ih =>
    change (a.inserted (p.rebuild h)).path ++ [(p.inserted h).branch] = a.path ++ [p.branch]
    rw [ih,p.inserted_branch]

theorem replace_inserted (a : ProofAddress root g) (h j : G P Θ Λ) :
    (a.inserted h).replace j = a.replace j := by
  induction a with
  | root => rfl
  | down a p ih =>
    change (a.inserted (p.rebuild h)).replace ((p.inserted h).rebuild j) = a.replace (p.rebuild j)
    rw [p.rebuild_inserted,ih]

/-- Concatenate occurrence addresses, preserving their branch sequences. -/
def append (a : ProofAddress root g) : {Ξ Ω : List (NormalForm P)} → {k : G P Ξ Ω} →
    ProofAddress g k → ProofAddress root k
  | _,_,_,.root => a
  | _,_,_,.down b p => (a.append b).down p

theorem append_root (a : ProofAddress root g) : a.append .root = a := rfl

theorem root_append (b : ProofAddress g k) : (.root : ProofAddress g g).append b = b := by
  induction b with
  | root => rfl
  | down b p ih => exact congrArg (fun c => c.down p) ih

theorem append_path (a : ProofAddress root g) (b : ProofAddress g k) :
    (a.append b).path = a.path ++ b.path := by
  induction b with
  | root => exact (List.append_nil _).symm
  | down b p ih =>
    change (a.append b).path ++ [p.branch] = a.path ++ (b.path ++ [p.branch])
    rw [ih,List.append_assoc]

theorem replace_append (a : ProofAddress root g) (b : ProofAddress g k) (h : G P Ξ Ω) :
    (a.append b).replace h = a.replace (b.replace h) := by
  induction b with
  | root => rfl
  | down b p ih => exact ih (p.rebuild h)

theorem append_assoc {I J : List (NormalForm P)} {j : G P I J}
    (a : ProofAddress root g) (b : ProofAddress g k) (c : ProofAddress k j) :
    (a.append b).append c = a.append (b.append c) := by
  induction c with
  | root => rfl
  | down c p ih => exact congrArg (fun a => a.down p) ih

theorem replace_denote (a : ProofAddress root g) (h : G P Θ Λ)
    (he : ofTerm h.denote = ofTerm g.denote) :
    ofTerm (a.replace h).denote = ofTerm root.denote := by
  induction a with
  | root => exact he
  | down a p ih => exact ih (p.rebuild h) (p.rebuild_denote h he)

theorem replace_relation (a : ProofAddress root g) (h : G P Θ Λ)
    (he : ofTerm h.denote = ofTerm g.denote) : (a.replace h).relation = root.relation :=
  congrArg occurrenceMap (a.replace_denote h he)

theorem replace_congr (a : ProofAddress root g) (h j : G P Θ Λ)
    (he : ofTerm h.denote = ofTerm j.denote) :
    ofTerm (a.replace h).denote = ofTerm (a.replace j).denote := by
  have ha := (a.inserted j).replace_denote h he
  rw [a.replace_inserted] at ha
  exact ha

theorem replace_cutCount (a : ProofAddress root g) (h : G P Θ Λ) :
    (a.replace h).cutCount + g.cutCount = root.cutCount + h.cutCount := by
  induction a with
  | root => exact Nat.add_comm ..
  | down a p ih =>
    have ha := ih (p.rebuild h)
    have hp := p.rebuild_cutCount h
    change (a.replace (p.rebuild h)).cutCount + _ = _
    omega

theorem replace_proofSize (a : ProofAddress root g) (h : G P Θ Λ) :
    (a.replace h).proofSize + g.proofSize = root.proofSize + h.proofSize := by
  induction a with
  | root => exact Nat.add_comm ..
  | down a p ih =>
    have ha := ih (p.rebuild h)
    have hp := p.rebuild_proofSize h
    change (a.replace (p.rebuild h)).proofSize + _ = _
    omega

theorem replace_count_eq (a : ProofAddress root g) (h : G P Θ Λ)
    (he : h.cutCount = g.cutCount) : (a.replace h).cutCount = root.cutCount := by
  have ha := a.replace_cutCount h
  omega

theorem replace_cutFree (a : ProofAddress root g) (h : G P Θ Λ)
    (hr : root.CutFree) (hh : h.CutFree) : (a.replace h).CutFree := by
  have ha := a.replace_cutCount h
  unfold G.CutFree at *
  omega

theorem replace_atomized (a : ProofAddress root g) (h : G P Θ Λ)
    (hr : root.Atomized) (hh : h.Atomized) : (a.replace h).Atomized := by
  induction a with
  | root => exact hh
  | down a p ih => exact ih (p.rebuild h) (p.rebuild_atomized h (a.atomized hr) hh)

end DosenPetric.Reduced.Gentzen.ProofAddress
