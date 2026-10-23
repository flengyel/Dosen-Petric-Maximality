module

public import DosenPetric.AtomicPadding

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced
universe u
variable {P : Type u}
namespace AtomicPorts

/-- Source B_top^n and C_bot^m, pp.320–321. -/
@[reducible] def unitObject (o : Op) (A : NormalForm P) : Nat → NormalForm P
  | 0 => A
  | n + 1 => unitObject o (o.formula A o.unit) n

def unitIn (A : NormalForm P) : (n : Nat) → Term P A (unitObject .conj A n)
  | 0 => .id A
  | n + 1 => .comp (.rightIn .conj A) (unitIn (.conj A .top) n)

def unitOut (A : NormalForm P) : (n : Nat) → Term P (unitObject .disj A n) A
  | 0 => .id A
  | n + 1 => .comp (unitOut (.disj A .bot) n) (.rightOut .disj A)

theorem unitIn_positive (A : NormalForm P) (n : Nat) : (unitIn A n).Positive := by
  induction n generalizing A with
  | zero => exact .id A
  | succ n ih => exact .comp (.rightIn ..) (ih _)

theorem unitOut_positive (A : NormalForm P) (n : Nat) : (unitOut A n).Positive := by
  induction n generalizing A with
  | zero => exact .id A
  | succ n ih => exact .comp (ih _) (.rightOut ..)

/-- Source iterated eta, with its identity accumulator generalized to f. -/
def etaTensor {A B : NormalForm P} (f : Term P A B) : (ps : List P) →
    Term P (unitObject .conj A ps.length) (expand .conj B ps)
  | [] => f
  | p :: ps => etaTensor (.tensor .conj f (.eta p)) ps

/-- Source iterated epsilon, with its identity accumulator generalized to f. -/
def epsilonTensor {A B : NormalForm P} (f : Term P A B) : (ps : List P) →
    Term P (expand .disj A ps) (unitObject .disj B ps.length)
  | [] => f
  | p :: ps => epsilonTensor (.tensor .disj f (.epsilon p)) ps

theorem eta_unit_bridge {A B : NormalForm P} (f : Term P A B) (p : P) :
    comp (rightIn .conj A) (tensor .conj (ofTerm f) (ofTerm (.eta p))) =
      comp (ofTerm f) (ofTerm (etaOne B p)) := by
  have h := etaOne_nat (ofTerm f) p (id (Atomic.etaObject p))
  change comp (comp (rightIn .conj A) (tensor .conj (id A) (ofTerm (.eta p))))
    (tensor .conj (ofTerm f) (id (Atomic.etaObject p))) = _ at h
  rw [Laws.assoc, Laws.tensor_comp, Laws.id_comp, Laws.comp_id] at h
  exact h

theorem epsilon_unit_bridge {A B : NormalForm P} (f : Term P A B) (p : P) :
    comp (tensor .disj (ofTerm f) (ofTerm (.epsilon p))) (rightOut .disj B) =
      comp (ofTerm (epsilonOne A p)) (ofTerm f) := by
  have h := epsilonOne_nat (ofTerm f) p (id (Atomic.epsilonObject p))
  change comp (tensor .disj (ofTerm f) (id (Atomic.epsilonObject p)))
    (comp (tensor .disj (id B) (ofTerm (.epsilon p))) (rightOut .disj B)) = _ at h
  rw [← Laws.assoc, Laws.tensor_comp, Laws.comp_id, Laws.id_comp] at h
  exact h

theorem etaTensor_units {A B : NormalForm P} (f : Term P A B) (ps : List P) :
    comp (ofTerm (unitIn A ps.length)) (ofTerm (etaTensor f ps)) =
      comp (ofTerm f) (ofTerm (etaPrefix B ps)) := by
  induction ps generalizing A B with
  | nil => change comp (id A) (ofTerm f) = comp (ofTerm f) (id B); rw [Laws.id_comp, Laws.comp_id]
  | cons p ps ih =>
    change comp (comp (rightIn .conj A) (ofTerm (unitIn (.conj A .top) ps.length)))
      (ofTerm (etaTensor (.tensor .conj f (.eta p)) ps)) = _
    rw [Laws.assoc, ih, ofTerm_tensor, ← Laws.assoc, eta_unit_bridge, Laws.assoc]
    rfl

theorem epsilonTensor_units {A B : NormalForm P} (f : Term P A B) (ps : List P) :
    comp (ofTerm (epsilonTensor f ps)) (ofTerm (unitOut B ps.length)) =
      comp (ofTerm (epsilonSuffix A ps)) (ofTerm f) := by
  induction ps generalizing A B with
  | nil => change comp (ofTerm f) (id B) = comp (id A) (ofTerm f); rw [Laws.comp_id, Laws.id_comp]
  | cons p ps ih =>
    change comp (ofTerm (epsilonTensor (.tensor .disj f (.epsilon p)) ps))
      (comp (ofTerm (unitOut (.disj B .bot) ps.length)) (rightOut .disj B)) = _
    rw [← Laws.assoc, ih, ofTerm_tensor, Laws.assoc, epsilon_unit_bridge, ← Laws.assoc]
    rfl

theorem prefix_separated (A : NormalForm P) (ps : List P) :
    ofTerm (etaPrefix A ps) = comp (ofTerm (unitIn A ps.length)) (ofTerm (etaTensor (.id A) ps)) := by
  have h := etaTensor_units (.id A) ps
  rw [ofTerm_id, Laws.id_comp] at h
  exact h.symm

theorem suffix_separated (A : NormalForm P) (ps : List P) :
    ofTerm (epsilonSuffix A ps) = comp (ofTerm (epsilonTensor (.id A) ps)) (ofTerm (unitOut A ps.length)) := by
  have h := epsilonTensor_units (.id A) ps
  rw [ofTerm_id, Laws.comp_id] at h
  exact h.symm

end AtomicPorts
end DosenPetric.Reduced
