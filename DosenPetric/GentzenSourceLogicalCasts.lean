module

public import DosenPetric.GentzenSelectedTerminalFactor

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace W4.NonemptyLeft
variable (d : SelectedLogical.Data P .conj) (hn : 1≤d.gs.length)
variable {F K : List (NormalForm P)} (hF : d.s.F=F) (hK : d.K=K)
variable (Δ : List (NormalForm P)) (f : G P (F++[d.A,d.B]) Δ)

def transported : G P K Δ :=
  (repair d hn Δ (f.reindex (congrArg (fun F=>F++[d.A,d.B]) hF).symm rfl)).reindex hK rfl

theorem transported_denote :
    ofTerm (transported d hn hF hK Δ f).denote=
      ofTerm ((d.outer.cast (congrArg (fun F=>F++[d.C]) hF) hK).applyL (outerArity d hn) Δ
        (G.conjL F [] Δ d.A d.B f)).denote := by
  cases hF;cases hK
  exact denote d hn Δ f

theorem transported_count : (transported d hn hF hK Δ f).cutCount=f.cutCount := by
  rw [transported,G.count_reindex,count,G.count_reindex]

theorem transported_bound :
    ContractionBound .left d.C
      (innerRank d hn Δ (f.reindex (congrArg (fun F=>F++[d.A,d.B]) hF).symm rfl)+1)
      (transported d hn hF hK Δ f) (fun a=>a.index=d.x.index) := by
  cases hF;cases hK
  exact repair_bound d hn Δ f
end W4.NonemptyLeft
namespace W4.NonemptyRight
variable (d : SelectedLogical.Data P .disj) (hn : 1≤d.gs.length)
variable {F K : List (NormalForm P)} (hF : d.s.F=F) (hK : d.K=K)
variable (Δ : List (NormalForm P)) (f : G P Δ (F++[d.A,d.B]))

def transported : G P Δ K :=
  (repair d hn Δ (f.reindex rfl (congrArg (fun F=>F++[d.A,d.B]) hF).symm)).reindex rfl hK

theorem transported_denote :
    ofTerm (transported d hn hF hK Δ f).denote=
      ofTerm ((d.outer.cast (congrArg (fun F=>F++[d.C]) hF) hK).applyR (outerArity d hn) Δ
        (G.disjR Δ F [] d.A d.B f)).denote := by
  cases hF;cases hK
  exact denote d hn Δ f

theorem transported_count : (transported d hn hF hK Δ f).cutCount=f.cutCount := by
  rw [transported,G.count_reindex,count,G.count_reindex]

theorem transported_bound :
    ContractionBound .right d.C
      (innerRank d hn Δ (f.reindex rfl (congrArg (fun F=>F++[d.A,d.B]) hF).symm)+1)
      (transported d hn hF hK Δ f) (fun a=>a.index=d.x.index) := by
  cases hF;cases hK
  exact repair_bound d hn Δ f
end W4.NonemptyRight
end DosenPetric.Reduced.Gentzen
