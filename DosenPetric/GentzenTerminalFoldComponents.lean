module

public import DosenPetric.GentzenBlockedLeftDisjHeadDenotation

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DosenPetric.Reduced.Gentzen.TerminalFold
universe u
variable {P : Type u}

theorem out_before {F : List (NormalForm P)} (A : NormalForm P) {B : NormalForm P} (b : At F B) :
    comp (out F A) (comp (fst (ante F) A) (ofTerm b.projection)) =
      ofTerm (b.before [A]).projection := by
  unfold out
  simp only [Laws.assoc]
  rw [← Laws.assoc (tensor .conj (id (ante F)) (rightOut .conj A)),← Laws.fst_nat,Laws.comp_id]
  have he := split_before .conj [A] b
  dsimp only [side,sideD,sideM,conjMonoidal,category,split,component,conjDiagonal] at he
  exact he

theorem out_last (F : List (NormalForm P)) (A : NormalForm P) :
    comp (out F A) (snd (ante F) A) = ofTerm (At.shift F (.here A [])).projection := by
  unfold out
  rw [Laws.assoc,← Laws.snd_nat]
  have he := split_shift .conj F (At.here A [])
  dsimp only [side,sideD,sideM,conjMonoidal,category,split,component,conjDiagonal] at he
  change comp (ofTerm (append .conj F [A]).invTerm)
    (comp (snd (ante F) (.conj A .top)) (fst A .top)) = _ at he
  rw [Laws.fst_top] at he
  exact he

theorem into_before {F : List (NormalForm P)} (A : NormalForm P) {B : NormalForm P} (b : At F B) :
    comp (into F A) (ofTerm (b.before [A]).projection) =
      comp (fst (ante F) A) (ofTerm b.projection) := by
  rw [← out_before A b,← Laws.assoc,into_out,Laws.id_comp]

theorem into_last (F : List (NormalForm P)) (A : NormalForm P) :
    comp (into F A) (ofTerm (At.shift F (.here A [])).projection) = snd (ante F) A := by
  rw [← out_last,← Laws.assoc,into_out,Laws.id_comp]

theorem join_before {F I : List (NormalForm P)} {B : NormalForm P} (b : At F B) :
    comp (ofTerm (append .conj F I).toTerm) (ofTerm (b.before I).projection) =
      comp (fst (ante F) (ante I)) (ofTerm b.projection) := by
  have he := Gentzen.join_before .conj b I
  dsimp only [side,sideD,sideM,conjMonoidal,category,join,component,conjDiagonal] at he
  exact he

theorem join_shift {F I : List (NormalForm P)} {B : NormalForm P} (b : At I B) :
    comp (ofTerm (append .conj F I).toTerm) (ofTerm (At.shift F b).projection) =
      comp (snd (ante F) (ante I)) (ofTerm b.projection) := by
  have he := Gentzen.join_shift .conj F b
  dsimp only [side,sideD,sideM,conjMonoidal,category,join,component,conjDiagonal] at he
  exact he

theorem split_before {F I : List (NormalForm P)} {B : NormalForm P} (b : At F B) :
    comp (ofTerm (append .conj F I).invTerm)
      (comp (fst (ante F) (ante I)) (ofTerm b.projection)) = ofTerm (b.before I).projection := by
  have he := Gentzen.split_before .conj I b
  dsimp only [side,sideD,sideM,conjMonoidal,category,split,component,conjDiagonal] at he
  exact he

theorem split_shift {F I : List (NormalForm P)} {B : NormalForm P} (b : At I B) :
    comp (ofTerm (append .conj F I).invTerm)
      (comp (snd (ante F) (ante I)) (ofTerm b.projection)) = ofTerm (At.shift F b).projection := by
  have he := Gentzen.split_shift .conj F b
  dsimp only [side,sideD,sideM,conjMonoidal,category,split,component,conjDiagonal] at he
  exact he

end DosenPetric.Reduced.Gentzen.TerminalFold

namespace DosenPetric.Reduced.Gentzen.BlockedLeftDisj
universe u
variable {P : Type u}

theorem terminalExchange_index (F : List (NormalForm P)) (A : NormalForm P) (I : List (NormalForm P))
    {B : NormalForm P} (b : At ((F++I)++[A]) B) :
    ((terminalExchange F A I).get b).index = exchangeIndex F.length I.length 1 b.index := by
  simp only [terminalExchange,ExchangeScript.get,ExchangeScript.rewire,Rewire.get,
    At.index_cast,swapBlocks_index,List.length_singleton]

theorem terminalExchange_before (F : List (NormalForm P)) (A : NormalForm P) (I : List (NormalForm P))
    {B : NormalForm P} (b : At F B) :
    (terminalExchange F A I).get ((b.before I).before [A]) = (b.before [A]).before I := by
  apply At.index_injective
  rw [terminalExchange_index]
  simp only [At.index_before]
  have hb := b.index_lt
  unfold exchangeIndex
  repeat first | split | omega

theorem terminalExchange_middle (F : List (NormalForm P)) (A : NormalForm P) (I : List (NormalForm P))
    {B : NormalForm P} (b : At I B) :
    (terminalExchange F A I).get ((At.shift F b).before [A]) = At.shift (F++[A]) b := by
  apply At.index_injective
  rw [terminalExchange_index]
  simp only [At.index_before,At.index_shift,List.length_append,List.length_singleton]
  have hb := b.index_lt
  unfold exchangeIndex
  repeat first | split | omega

theorem terminalExchange_last (F : List (NormalForm P)) (A : NormalForm P) (I : List (NormalForm P)) :
    (terminalExchange F A I).get (At.shift (F++I) (.here A [])) =
      (At.shift F (.here A [])).before I := by
  apply At.index_injective
  rw [terminalExchange_index]
  simp only [At.index_before,At.index_shift,At.index,List.length_append,Nat.add_zero]
  unfold exchangeIndex
  repeat first | split | omega

end DosenPetric.Reduced.Gentzen.BlockedLeftDisj
