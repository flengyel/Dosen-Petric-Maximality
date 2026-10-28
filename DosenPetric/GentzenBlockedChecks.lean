module

public import DosenPetric.GentzenBlockedNormalization
public import DosenPetric.GentzenSameSideLogicalExamples
public import DosenPetric.GentzenReducibleExamples

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.BlockedChecks
open BlockedSource

def lowerLeft (D : NormalForm Empty) (Γ : List (NormalForm Empty)) : G Empty (D::Γ) [.top] :=
  G.contractL D [[],[]] Γ [.top] (Nat.le_refl 2) (W1.SameSideLogical.constantLeft (D::D::Γ))
def lowerRight (D : NormalForm Empty) (Δ : List (NormalForm Empty)) : G Empty [.bot] (D::Δ) :=
  G.contractR [.bot] D [[],[]] Δ (Nat.le_refl 2) (W1.SameSideLogical.constantRight (D::D::Δ))

structure CaseL where
  source : List (NormalForm Empty)
  target : List (NormalForm Empty)
  proof : G Empty source target
  blocked : BlockedL proof
structure CaseR where
  source : List (NormalForm Empty)
  target : List (NormalForm Empty)
  proof : G Empty source target
  blocked : BlockedR proof

def mixL : CaseL := ⟨_,_,_,.gammaMix .top [] [] [] [] [.top] [.top] (lowerLeft .top []) (lowerLeft .top [])⟩
def conjL : CaseL := ⟨_,_,_,.gammaConj .top .top .top [] [] [] [] [] [] (lowerLeft .top []) (lowerLeft .top [])⟩
def disjL : CaseL := ⟨_,_,_,.gammaDisj .top .top .bot [] [] [] [] [.top] [.top] (lowerLeft .top [.top]) (lowerLeft .top [.bot])⟩
def conjunctionL : CaseL := ⟨_,_,_,.conjunction .top .bot [] [] [.top] (lowerLeft (.conj .top .bot) [.top,.bot])⟩
def firstL : CaseL := ⟨_,_,_,.disjunctionFirst .top .bot [] [] [] [.top] [.top] (lowerLeft (.disj .top .bot) [.top]) (lowerLeft .bot [])⟩
def secondL : CaseL := ⟨_,_,_,.disjunctionSecond .top .bot [] [] [] [.top] [.top] (lowerLeft .top []) (lowerLeft (.disj .top .bot) [.bot])⟩
def bothL : CaseL := ⟨_,_,_,.disjunctionBoth .top .bot [] [] [] [] [.top] [.top] (lowerLeft (.disj .top .bot) [.top]) (lowerLeft (.disj .top .bot) [.bot])⟩
def mixR : CaseR := ⟨_,_,_,.gammaMix .top [.bot] [.bot] [] [] [] [] (lowerRight .top []) (lowerRight .top [])⟩
def disjR : CaseR := ⟨_,_,_,.gammaDisj .top .bot .bot [] [] [] [] [] [] (lowerRight .top []) (lowerRight .top [])⟩
def conjR : CaseR := ⟨_,_,_,.gammaConj .top .bot .bot [.bot] [.bot] [] [] [] [] (lowerRight .bot [.top]) (lowerRight .bot [.top])⟩
def disjunctionR : CaseR := ⟨_,_,_,.disjunction .bot .bot [.bot] [] [] (lowerRight .bot [.bot,.disj .bot .bot])⟩
def firstR : CaseR := ⟨_,_,_,.conjunctionFirst .bot .bot [.bot] [.bot] [] [] [] (lowerRight .bot [.conj .bot .bot]) (lowerRight .bot [])⟩
def secondR : CaseR := ⟨_,_,_,.conjunctionSecond .bot .bot [.bot] [.bot] [] [] [] (lowerRight .bot []) (lowerRight .bot [.conj .bot .bot])⟩
def bothR : CaseR := ⟨_,_,_,.conjunctionBoth .bot .bot [.bot] [.bot] [] [] [] [] (lowerRight .bot [.conj .bot .bot]) (lowerRight .bot [.conj .bot .bot])⟩

def lowerPaths {Γ Δ : List (NormalForm Empty)} (g : G Empty Γ Δ) (s : SequentSide) : List (List Nat) :=
  (g.occurrences.filter (fun o => decide (o.proof.ruleKind =
    match s with | .left => .contractL | .right => .contractR))).map (fun o => o.address.path)

/-- All fourteen envelopes contain the actual lower-contraction roots of every
free premise; the two identical mix premises retain distinct paths. -/
theorem all_fourteen_paths :
    ([mixL,conjL,disjL,conjunctionL,firstL,secondL,bothL].map (fun c => lowerPaths c.proof .left)) =
      [[[],[0,0],[0,1]], [[],[0,0],[0,1]], [[],[0,0,0,0],[0,0,1,0]],
       [[],[0,0]], [[],[0,0,0,0],[0,0,1,0]], [[],[0,0,0,0],[0,0,1,0]], [[],[0,0,0,0],[0,0,1,0]]] ∧
    ([mixR,disjR,conjR,disjunctionR,firstR,secondR,bothR].map (fun c => lowerPaths c.proof .right)) =
      [[[],[0,0],[0,1]], [[],[0,0,0,0],[0,0,1,0]], [[],[0,0],[0,1]],
       [[],[0,0]], [[],[0,0],[0,1]], [[],[0,0],[0,1]], [[],[0,0],[0,1]]] := by decide

theorem every_left_replacement (c : CaseL) {U V : List (NormalForm Empty)} {w : G Empty U V}
    (a : ProofAddress c.proof w) (hp : a.path ≠ []) {D : NormalForm Empty}
    (x : At U D) (hw : w.LowerContraction .left x) (h : G Empty U V) :
    BlockedL (a.replace h) := c.blocked.replace_lower a hp x hw h

theorem every_right_replacement (c : CaseR) {U V : List (NormalForm Empty)} {w : G Empty U V}
    (a : ProofAddress c.proof w) (hp : a.path ≠ []) {D : NormalForm Empty}
    (x : At V D) (hw : w.LowerContraction .right x) (h : G Empty U V) :
    BlockedR (a.replace h) := c.blocked.replace_lower a hp x hw h

def nestedEmptyExchange : CaseL :=
  ⟨_,_,_,.gammaMix .top [] [] [] [] [.top] [.top]
    (G.exchangeL [] [] [] [.top] [.top] (lowerLeft .top []))
    (G.exchangeL [] [] [] [.top] [.top] (lowerLeft .top []))⟩

/-- Actual empty exchanges add nodes, including above identical siblings. -/
theorem nested_empty_exchange_paths : lowerPaths nestedEmptyExchange.proof .left =
    [[],[0,0,0],[0,1,0]] := by decide

universe u
variable {P : Type u}

def common (t : Literal P) : G P [.lit t] [.lit t,.lit t] :=
  left2 (.lit t) [] [] [] [.lit t,.lit t]
    (G.mix (ReducibleExamples.left t) (ReducibleExamples.left t))

theorem common_blocked (t : Literal P) : BlockedL (common t) :=
  .gammaMix (.lit t) [] [] [] [] [.lit t] [.lit t]
    (ReducibleExamples.left t) (ReducibleExamples.left t)

def firstAddress (t : Literal P) : ProofAddress (common t) (ReducibleExamples.left t) :=
  (ProofAddress.root.down (Premise.contractL (.lit t) [[],[]] [] [.lit t,.lit t] (Nat.le_refl 2)
    (G.mix (ReducibleExamples.left t) (ReducibleExamples.left t)))).down
    (Premise.mix_left (ReducibleExamples.left t) (ReducibleExamples.left t))

def secondAddress (t : Literal P) : ProofAddress (common t) (ReducibleExamples.left t) :=
  (ProofAddress.root.down (Premise.contractL (.lit t) [[],[]] [] [.lit t,.lit t] (Nat.le_refl 2)
    (G.mix (ReducibleExamples.left t) (ReducibleExamples.left t)))).down
    (Premise.mix_right (ReducibleExamples.left t) (ReducibleExamples.left t))

theorem common_paths (t : Literal P) :
    (firstAddress t).path = [0,0] ∧ (secondAddress t).path = [0,1] := ⟨rfl,rfl⟩

theorem common_tied (t : Literal P) :
    (common t).TiedRight ((firstAddress t).traceAt .left (.here (.lit t) [])) ∧
    (common t).TiedRight ((secondAddress t).traceAt .left (.here (.lit t) [])) := by
  constructor
  all_goals constructor
  all_goals first
    | (apply (ProofAddress.cluster_iff_ascend _ .left (.here (.lit t) []) _).mpr; rfl)
    | exact .left ..

/-- The common blocked ancestor survives repairing either proper contraction. -/
theorem common_preserved (t : Literal P) (h : G P [.lit t] [.lit t]) :
    BlockedL ((firstAddress t).replace h) ∧ BlockedL ((secondAddress t).replace h) := by
  constructor
  · exact (common_blocked t).replace_lower _ (by intro he; cases he)
      (.here (.lit t) []) (G.LowerContraction.left ..) h
  · exact (common_blocked t).replace_lower _ (by intro he; cases he)
      (.here (.lit t) []) (G.LowerContraction.left ..) h

theorem common_shallow_blocked (t : Literal P)
    {U V : List (NormalForm P)} {w : G P U V}
    (b : ProofAddress (common t) w) (y : At U (.lit t))
    (hy : (common t).TiedRight (b.traceAt .left y)) (hl : b.path.length < 2) : BlockedL w := by
  rw [← b.spine_toAddress] at hy
  rw [← b.spine_path] at hl
  cases hs : b.spine with
  | root => exact common_blocked t
  | down p c =>
    rw [hs] at hy hl
    have he := G.branches_complete (⟨_,_,_,p⟩ : Branch _)
    simp only [common,BlockedSource.left2,G.branches,List.mem_cons,List.not_mem_nil,or_false] at he
    cases he
    cases c with
    | root =>
      have hh := (G.lowerContraction_iff_arity _ .left y).mp hy.2
      change 2 ≤ 1 at hh
      omega
    | down q d =>
      simp only [ProofSpine.path,List.length_cons] at hl
      omega

theorem common_eligible (t : Literal P) :
    ReducibleL (G.identity t) (common t) (firstAddress t) (.here (.lit t) []) ∧
    ReducibleL (G.identity t) (common t) (secondAddress t) (.here (.lit t) []) := by
  constructor
  all_goals refine ⟨⟨rfl,rfl⟩,?_,ReducibleExamples.left_unblocked t,?_⟩
  · exact (common_tied t).1
  · intro U V w b y hy hp
    exact common_shallow_blocked t b y hy (ProofAddress.proper_length hp)
  · exact (common_tied t).2
  · intro U V w b y hy hp
    exact common_shallow_blocked t b y hy (ProofAddress.proper_length hp)

/-- Inserting no ranks, one rank, or several smaller ranks is allowed even
when several unchanged sites have the same maximal rank. -/
theorem multiset_boundaries :
    FiniteRank.Descent [7,7,3] [3,7,7,3] ∧
    FiniteRank.Descent [2,7,7,3] [3,7,7,3] ∧
    FiniteRank.Descent [2,2,2,1,0,7,7,3] [3,7,7,3] := by
  refine ⟨?_,?_,?_⟩
  · exact FiniteRank.of_replacement (outside := [7,7,3]) (inserted := [])
      (List.Perm.refl _) (List.Perm.refl _) (by decide)
  · exact FiniteRank.of_replacement (outside := [7,7,3]) (inserted := [2])
      (List.Perm.refl _) (List.Perm.refl _) (by decide)
  · exact FiniteRank.of_replacement (outside := [7,7,3]) (inserted := [2,2,2,1,0])
      (List.Perm.refl _) (List.Perm.refl _) (by decide)

end DosenPetric.Reduced.Gentzen.BlockedChecks
