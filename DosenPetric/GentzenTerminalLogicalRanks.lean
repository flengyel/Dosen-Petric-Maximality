module

public import DosenPetric.GentzenBinaryLogicalRanks
public import DosenPetric.GentzenSourceLogicalBlocked

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen.BlockedSource
universe u
variable {P : Type u}

def headL {F Δ : List (NormalForm P)} (A : NormalForm P) (f : G P (F++[A]) Δ) : G P (A::F) Δ :=
  UnaryCast.exchangeL [] F [A] []
    (by simp only [List.nil_append,List.append_nil])
    (by simp only [List.nil_append,List.singleton_append,List.append_nil]) Δ f

def tailL {F Δ : List (NormalForm P)} (A : NormalForm P) (f : G P (A::F) Δ) : G P (F++[A]) Δ :=
  UnaryCast.exchangeL [] [A] F []
    (by simp only [List.nil_append,List.singleton_append,List.append_nil])
    (by simp only [List.nil_append,List.append_nil]) Δ f

theorem headL_rank {F Δ : List (NormalForm P)} (A : NormalForm P) (f : G P (F++[A]) Δ)
    {C : NormalForm P} (a : At F C) :
    (headL A f).rho .left (.there a)=1+f.rho .left (a.before [A]) := by
  have h:=UnaryCast.exchangeL_embedded (U:=A::F) [] F [A] []
    (by simp only [List.nil_append,List.append_nil])
    (by simp only [List.nil_append,List.singleton_append,List.append_nil]) Δ f (a.before [A])
  change (headL A f).rho .left ((Route.toHead F A).get (a.before [A]))=_ at h
  rw [Route.toHead_before] at h
  exact h

theorem tailL_rank {F Δ : List (NormalForm P)} (A : NormalForm P) (f : G P (A::F) Δ)
    {C : NormalForm P} (a : At (A::F) C) :
    (tailL A f).rho .left ((Route.toTail F A).get a)=1+f.rho .left a :=
  UnaryCast.exchangeL_embedded [] [A] F []
    (by simp only [List.nil_append,List.singleton_append,List.append_nil])
    (by simp only [List.nil_append,List.append_nil]) Δ f a

theorem disjLLast_eq {F U Δ Λ : List (NormalForm P)} {A B : NormalForm P}
    (f : G P (F++[A]) Δ) (g : G P (U++[B]) Λ) :
    disjLLast f g=tailL (.disj A B) (G.disjL (headL A f) (headL B g)) := rfl

variable {F U Δ Λ : List (NormalForm P)} {A B : NormalForm P}
variable (f : G P (F++[A]) Δ) (g : G P (U++[B]) Λ)

theorem disjLLast_rank_f {C : NormalForm P} (a : At F C) :
    (disjLLast f g).rho .left ((a.before U).before [.disj A B])=
      3+f.rho .left (a.before [A]) := by
  rw [disjLLast_eq]
  have h:=tailL_rank (.disj A B) (G.disjL (headL A f) (headL B g)) (.there (a.before U))
  rw [Route.toTail_there,G.rho_disjL_f,headL_rank] at h
  omega

theorem disjLLast_rank_g {C : NormalForm P} (a : At U C) :
    (disjLLast f g).rho .left ((At.shift F a).before [.disj A B])=
      3+g.rho .left (a.before [B]) := by
  rw [disjLLast_eq]
  have h:=tailL_rank (.disj A B) (G.disjL (headL A f) (headL B g)) (.there (At.shift F a))
  rw [Route.toTail_there,G.rho_disjL_g,headL_rank] at h
  omega

theorem disjLLast_rank_principal :
    (disjLLast f g).rho .left (At.shift (F++U) (.here (.disj A B) []))=2 := by
  rw [disjLLast_eq]
  have h:=tailL_rank (.disj A B) (G.disjL (headL A f) (headL B g)) (.here (.disj A B) (F++U))
  rw [Route.toTail_here] at h
  have hl : (G.disjL (headL A f) (headL B g)).rho .left (.here (.disj A B) (F++U))=1 :=
    G.rho_leaf _ .left _ (by rfl)
  omega

end DosenPetric.Reduced.Gentzen.BlockedSource
