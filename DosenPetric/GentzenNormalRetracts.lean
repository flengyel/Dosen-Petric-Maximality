module

public import DosenPetric.GentzenNormalFormCoherence
public import DosenPetric.GentzenDistributiveMono

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

theorem normal_represented_coherence {A B : NormalForm P} (d : DNF A) (c : CNF B)
    (f g : Hom A B) (hf : Represented f) (hg : Represented g)
    (h : occurrenceMap f = occurrenceMap g) : f = g := by
  obtain ⟨a,ea⟩ := hf
  obtain ⟨b,eb⟩ := hg
  let ta : Term P A B := .comp (.rightIn .conj A) (.comp a.denote (.rightOut .disj B))
  let tb : Term P A B := .comp (.rightIn .conj A) (.comp b.denote (.rightOut .disj B))
  have pa : ta.Positive := .comp (.rightIn ..) (.comp a.denote_positive (.rightOut ..))
  have pb : tb.Positive := .comp (.rightIn ..) (.comp b.denote_positive (.rightOut ..))
  have ra : ofTerm ta = f := ea
  have rb : ofTerm tb = g := eb
  have hr : ta.relation = tb.relation := by
    change occurrenceMap (ofTerm ta) = occurrenceMap (ofTerm tb)
    rw [ra,rb,h]
  exact ra.symm.trans ((normal_positive_coherence d c ta tb pa pb hr).trans rb)

/-- Only the original object is a retract of the expanded one. A second inverse
equation is neither assumed nor required by distributive normalization. -/
structure NormalRetract (A B : NormalForm P) where
  forward : Hom A B
  backward : Hom B A
  forward_represented : Represented forward
  backward_represented : Represented backward
  recover : comp forward backward = id A

namespace NormalRetract

def refl (A : NormalForm P) : NormalRetract A A :=
  ⟨id A,id A,Represented.identity A,Represented.identity A,Laws.id_comp _⟩

def trans {A B C : NormalForm P} (r : NormalRetract A B) (s : NormalRetract B C) :
    NormalRetract A C where
  forward := comp r.forward s.forward
  backward := comp s.backward r.backward
  forward_represented := r.forward_represented.comp s.forward_represented
  backward_represented := s.backward_represented.comp r.backward_represented
  recover := by rw [Laws.assoc,← Laws.assoc s.forward,s.recover,Laws.id_comp,r.recover]

def tensor (o : Op) {A B C D : NormalForm P} (r : NormalRetract A B) (s : NormalRetract C D) :
    NormalRetract (o.formula A C) (o.formula B D) where
  forward := Reduced.tensor o r.forward s.forward
  backward := Reduced.tensor o r.backward s.backward
  forward_represented := r.forward_represented.tensor o s.forward_represented
  backward_represented := r.backward_represented.tensor o s.backward_represented
  recover := by rw [Laws.tensor_comp,r.recover,s.recover,Laws.tensor_id]

def swap (o : Op) (A B : NormalForm P) : NormalRetract (o.formula A B) (o.formula B A) :=
  ⟨Reduced.swap o A B,Reduced.swap o B A,Represented.swap o A B,
    Represented.swap o B A,Laws.swap_swap o A B⟩

def dnfRight (X A B : NormalForm P) :
    NormalRetract (.conj X (.disj A B)) (.disj (.conj X A) (.conj X B)) where
  forward := DistributiveEpi.sectionMap X A B
  backward := DistributiveEpi.comparison X A B
  forward_represented :=
    ((Represented.diag X).tensor .conj (Represented.identity (.disj A B))).comp
      (positive_represented _ (Rules.sourceConj_positive X X A B))
  backward_represented :=
    ((Represented.identity X).tensor .conj (Represented.inl A B)).copair
      ((Represented.identity X).tensor .conj (Represented.inr A B))
  recover := DistributiveEpi.section_comparison X A B

def dnfLeft (A B X : NormalForm P) :
    NormalRetract (.conj (.disj A B) X) (.disj (.conj A X) (.conj B X)) :=
  ((swap .conj (.disj A B) X).trans (dnfRight X A B)).trans
    ((swap .conj X A).tensor .disj (swap .conj X B))

def cnfLeft (A B X : NormalForm P) :
    NormalRetract (.disj (.conj A B) X) (.conj (.disj A X) (.disj B X)) where
  forward := DistributiveMono.comparison A B X
  backward := DistributiveMono.retraction A B X
  forward_represented :=
    ((Represented.fst A B).tensor .disj (Represented.identity X)).pair
      ((Represented.snd A B).tensor .disj (Represented.identity X))
  backward_represented :=
    (positive_represented _ (Rules.mixedDisj_positive A X B X)).comp
      ((Represented.identity (.conj A B)).tensor .disj (Represented.codiag X))
  recover := DistributiveMono.comparison_retraction A B X

def cnfRight (X A B : NormalForm P) :
    NormalRetract (.disj X (.conj A B)) (.conj (.disj X A) (.disj X B)) :=
  ((swap .disj X (.conj A B)).trans (cnfLeft A B X)).trans
    ((swap .disj A X).tensor .conj (swap .disj B X))

end NormalRetract
end DosenPetric.Reduced.Gentzen
