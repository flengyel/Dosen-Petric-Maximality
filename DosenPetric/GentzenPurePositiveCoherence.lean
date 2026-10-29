module

public import DosenPetric.GentzenMixNormalForm

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

/-- Restricted positive coherence at conjunction-only/disjunction-only endpoints,
with constants, signed literals, repeated tags and witnessed empty relations. -/
theorem pure_positive_coherence {A B : NormalForm P} (f g : Term P A B)
    (hf : f.Positive) (hg : g.Positive) (hA : Pure .conj A) (hB : Pure .disj B)
    (h : f.relation = g.relation) : ofTerm f = ofTerm g := by
  obtain ⟨a,_,_,ma,ea,ra⟩ := positive_mix_represented f hf hA hB
  obtain ⟨b,_,_,mb,eb,rb⟩ := positive_mix_represented g hg hA hB
  have hr : a.relation = b.relation := by
    funext x y
    apply propext
    have ha := ra (singletonFrom .conj A x) (singletonFrom .disj B y)
    have hb := rb (singletonFrom .conj A x) (singletonFrom .disj B y)
    rw [singletonOcc_from,singletonOcc_from] at ha hb
    rw [h] at ha
    exact ha.trans hb.symm
  have he := ea.symm.trans ((a.mix_faithful b ma mb hr).trans eb)
  have hd := congrArg (fun k => comp (rightIn .conj A) (comp k (rightOut .disj B))) he
  change decode (encode f) = decode (encode g) at hd
  rw [decode_encode,decode_encode] at hd
  exact hd

end DosenPetric.Reduced.Gentzen
