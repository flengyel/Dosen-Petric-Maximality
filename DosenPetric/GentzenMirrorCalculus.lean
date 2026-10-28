module

public import DosenPetric.GentzenPrincipalConjunctionSelected

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

/-- Reverse each binary connective and interchange its two arguments. -/
def mirror : NormalForm P → NormalForm P
  | .lit l => .lit l
  | .top => .bot
  | .bot => .top
  | .conj A B => .disj (mirror B) (mirror A)
  | .disj A B => .conj (mirror B) (mirror A)

theorem mirror_involutive (A : NormalForm P) : mirror (mirror A) = A := by
  induction A <;> simp only [mirror, *]

/- A concrete interpretation of diagram equations in the opposite category,
reindexed on objects by mirror. It asserts no operation on quotient arrows. -/
namespace MirrorCalculus

def Hom (A B : NormalForm P) := Reduced.Hom (mirror B) (mirror A)
def id (A : NormalForm P) : Hom A A := Reduced.id (mirror A)
def comp {A B C : NormalForm P} (f : Hom A B) (g : Hom B C) : Hom A C := Reduced.comp g f

def tensor (o : Op) {A B C D : NormalForm P} (f : Hom A C) (g : Hom B D) :
    Hom (o.formula A B) (o.formula C D) :=
  match o with
  | .conj => Reduced.tensor .disj g f
  | .disj => Reduced.tensor .conj g f

def assocR (o : Op) (A B C : NormalForm P) :
    Hom (o.formula A (o.formula B C)) (o.formula (o.formula A B) C) :=
  match o with
  | .conj => Reduced.assocR .disj (mirror C) (mirror B) (mirror A)
  | .disj => Reduced.assocR .conj (mirror C) (mirror B) (mirror A)

def assocL (o : Op) (A B C : NormalForm P) :
    Hom (o.formula (o.formula A B) C) (o.formula A (o.formula B C)) :=
  match o with
  | .conj => Reduced.assocL .disj (mirror C) (mirror B) (mirror A)
  | .disj => Reduced.assocL .conj (mirror C) (mirror B) (mirror A)

def swap (o : Op) (A B : NormalForm P) : Hom (o.formula A B) (o.formula B A) :=
  match o with
  | .conj => Reduced.swap .disj (mirror A) (mirror B)
  | .disj => Reduced.swap .conj (mirror A) (mirror B)

def dist (A B C : NormalForm P) : Hom (.conj A (.disj B C)) (.disj (.conj A B) C) :=
  Reduced.dist (mirror C) (mirror B) (mirror A)

def fst (A B : NormalForm P) : Hom (.conj A B) A := Reduced.inr (mirror B) (mirror A)
def snd (A B : NormalForm P) : Hom (.conj A B) B := Reduced.inl (mirror B) (mirror A)
def pair {X A B : NormalForm P} (f : Hom X A) (g : Hom X B) : Hom X (.conj A B) :=
  Reduced.copair g f

namespace Laws

theorem id_comp {A B : NormalForm P} (f : Hom A B) : comp (id A) f = f :=
  Reduced.Laws.comp_id f

theorem comp_id {A B : NormalForm P} (f : Hom A B) : comp f (id B) = f :=
  Reduced.Laws.id_comp f

theorem assoc {A B C D : NormalForm P} (f : Hom A B) (g : Hom B C) (h : Hom C D) :
    comp (comp f g) h = comp f (comp g h) := (Reduced.Laws.assoc h g f).symm

theorem tensor_id (o : Op) (A B : NormalForm P) : tensor o (id A) (id B) = id (o.formula A B) := by
  cases o <;> exact Reduced.Laws.tensor_id _ _ _

theorem tensor_comp (o : Op) {A B C D E F : NormalForm P}
    (f : Hom A C) (g : Hom B D) (h : Hom C E) (k : Hom D F) :
    comp (tensor o f g) (tensor o h k) = tensor o (comp f h) (comp g k) := by
  cases o <;> exact Reduced.Laws.tensor_comp _ k h g f

theorem assocR_L (o : Op) (A B C : NormalForm P) :
    comp (assocR o A B C) (assocL o A B C) = id (o.formula A (o.formula B C)) := by
  cases o <;> exact Reduced.Laws.assocL_R _ _ _ _

theorem assocL_R (o : Op) (A B C : NormalForm P) :
    comp (assocL o A B C) (assocR o A B C) = id (o.formula (o.formula A B) C) := by
  cases o <;> exact Reduced.Laws.assocR_L _ _ _ _

theorem assocR_nat (o : Op) {A B C D E F : NormalForm P}
    (f : Hom A D) (g : Hom B E) (h : Hom C F) :
    comp (assocR o A B C) (tensor o (tensor o f g) h) =
      comp (tensor o f (tensor o g h)) (assocR o D E F) := by
  cases o with
  | conj => exact (Reduced.Laws.assocR_nat .disj h g f).symm
  | disj => exact (Reduced.Laws.assocR_nat .conj h g f).symm

theorem assocL_nat (o : Op) {A B C D E F : NormalForm P}
    (f : Hom A D) (g : Hom B E) (h : Hom C F) :
    comp (assocL o A B C) (tensor o f (tensor o g h)) =
      comp (tensor o (tensor o f g) h) (assocL o D E F) := by
  cases o with
  | conj => exact (Reduced.Laws.assocL_nat .disj h g f).symm
  | disj => exact (Reduced.Laws.assocL_nat .conj h g f).symm

theorem swap_nat (o : Op) {A B C D : NormalForm P} (f : Hom A C) (g : Hom B D) :
    comp (swap o A B) (tensor o g f) = comp (tensor o f g) (swap o C D) := by
  cases o with
  | conj => exact (Reduced.Laws.swap_nat .disj f g).symm
  | disj => exact (Reduced.Laws.swap_nat .conj f g).symm

theorem dist_nat {A B C D E F : NormalForm P} (f : Hom A D) (g : Hom B E) (h : Hom C F) :
    comp (dist A B C) (tensor .disj (tensor .conj f g) h) =
      comp (tensor .conj f (tensor .disj g h)) (dist D E F) :=
  (Reduced.Laws.dist_nat h g f).symm

theorem dist_conj (A B C D : NormalForm P) :
    dist (.conj A B) C D =
      comp (assocL .conj A B (.disj C D))
        (comp (tensor .conj (id A) (dist B C D))
          (comp (dist A (.conj B C) D) (tensor .disj (assocR .conj A B C) (id D)))) := by
  simpa only [Hom, dist, mirror, comp, tensor, assocL, assocR, id, Reduced.Laws.assoc] using
    Reduced.Laws.dist_disj (mirror D) (mirror C) (mirror B) (mirror A)

theorem dist_disj (A B C D : NormalForm P) :
    dist A B (.disj C D) =
      comp (tensor .conj (id A) (assocR .disj B C D))
        (comp (dist A (.disj B C) D)
          (comp (tensor .disj (dist A B C) (id D)) (assocL .disj (.conj A B) C D))) := by
  simpa only [Hom, dist, mirror, comp, tensor, assocL, assocR, id, Reduced.Laws.assoc] using
    Reduced.Laws.dist_conj (mirror D) (mirror C) (mirror B) (mirror A)

theorem fst_nat {A B C D : NormalForm P} (f : Hom A C) (g : Hom B D) :
    comp (fst A B) f = comp (tensor .conj f g) (fst C D) :=
  (Reduced.Laws.inr_nat g f).symm

theorem snd_nat {A B C D : NormalForm P} (f : Hom A C) (g : Hom B D) :
    comp (snd A B) g = comp (tensor .conj f g) (snd C D) :=
  (Reduced.Laws.inl_nat g f).symm

theorem snd_swap (A B : NormalForm P) : snd A B = comp (swap .conj A B) (fst B A) :=
  (inr_then_swap (mirror A) (mirror B)).symm

end Laws
theorem swap_snd (A B : NormalForm P) : comp (swap .conj A B) (snd B A) = fst A B :=
  (Reduced.Laws.inr_swap (mirror B) (mirror A)).symm

theorem tensor_factor (o : Op) {A B C D E : NormalForm P}
    (f : Hom A B) (g : Hom C D) (h : Hom D E) :
    tensor o f (comp g h) = comp (tensor o f g) (tensor o (id B) h) := by
  rw [Laws.tensor_comp, Laws.comp_id]

def mixedDisj (A D B E : NormalForm P) :
    Hom (.conj (.disj A D) (.disj B E)) (.disj (.conj A B) (.disj D E)) :=
  comp (dist (.disj A D) B E)
    (comp (tensor .disj
      (comp (swap .conj (.disj A D) B)
        (comp (dist B A D) (tensor .disj (swap .conj B A) (id D)))) (id E))
      (assocL .disj (.conj A B) D E))

end MirrorCalculus
end DosenPetric.Reduced.Gentzen
