module

public import DosenPetric.GentzenContractionSelection
public import Init.Data.List.Perm

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}

namespace TraceRoute
theorem fiber_nodup {Γ Δ : List (NormalForm P)} {C : NormalForm P}
    (w : TraceRoute Γ Δ) (x : At Γ C) : (w.fiber x).Nodup := by
  apply (fiber_ordered w x).imp
  intro a b hab he
  cases he
  omega

/-- The grouped intermediate fibers retain exactly the original preimages.
Their order can differ, so this statement is a permutation, not list equality. -/
theorem fiber_comp_perm {F I K : List (NormalForm P)} (p : Route I F) (q : Route K I)
    {C : NormalForm P} (x : At K C) :
    List.Perm (((full q).fiber x).flatMap (fun b => (full p).fiber b))
      ((full (p.map q.get)).fiber x) := by
  have hn : (((full q).fiber x).flatMap (fun b => (full p).fiber b)).Nodup := by
    apply List.pairwise_flatMap.mpr
    constructor
    · intro b _; exact fiber_nodup _ _
    · apply (fiber_nodup (full q) x).imp
      intro b c hbc a ha d hd he
      cases he
      have hb := (fiber_correct (full p) b a).mp ha
      have hc := (fiber_correct (full p) c a).mp hd
      rw [get_full] at hb hc
      exact hbc ((Option.some.inj hb).symm.trans (Option.some.inj hc))
  apply (List.perm_ext_iff_of_nodup hn (fiber_nodup _ _)).mpr
  intro a
  rw [List.mem_flatMap,fiber_correct,get_full,Option.some.injEq,Route.get_map]
  constructor
  · rintro ⟨b,hb,ha⟩
    have hp := (fiber_correct (full p) b a).mp ha
    have hq := (fiber_correct (full q) x b).mp hb
    rw [get_full,Option.some.injEq] at hp hq
    exact (congrArg q.get hp).trans hq
  · intro h
    exact ⟨p.get a,(fiber_correct (full q) x _).mpr (by rw [get_full,h]),
      (fiber_correct (full p) _ a).mpr (get_full p a)⟩

theorem sum_flatMap_map {α β : Type u} (xs : List α) (f : α → List β) (r : β → Nat) :
    ((xs.flatMap f).map r).sum = (xs.map (fun a => ((f a).map r).sum)).sum := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp only [List.flatMap_cons,List.map_append,List.sum_append,
      List.map_cons,List.sum_cons,ih]

theorem sum_fiber_comp {F I K : List (NormalForm P)} (p : Route I F) (q : Route K I)
    {C : NormalForm P} (x : At K C) (r : At F C → Nat) :
    (((full (p.map q.get)).fiber x).map r).sum =
      (((full q).fiber x).map (fun b => (((full p).fiber b).map r).sum)).sum :=
  ((fiber_comp_perm p q x).map r).sum_nat.symm.trans (sum_flatMap_map _ _ _)
end TraceRoute

namespace ContractionBlock
variable {F K : List (NormalForm P)} (d : ContractionBlock P F K)

theorem selected_fiber : (TraceRoute.full d.route).fiber d.keep = d.selected := by
  apply At.ordered_ext _ _ (TraceRoute.fiber_ordered _ _) d.selected_ordered
  intro a
  rw [TraceRoute.fiber_correct,TraceRoute.get_full,Option.some.injEq,d.selected_iff]

theorem rankL_fiber (hn : 2 ≤ d.gs.length) (Δ : List (NormalForm P))
    (f : G P F Δ) {A : NormalForm P} (a : At K A) :
    (d.applyL hn Δ f).rho .left a =
      1+(((TraceRoute.full d.route).fiber a).map (fun b => f.rho .left b)).sum := by
  cases At.compare a d.keep with
  | same => rw [d.selected_fiber,d.rankL_keep,d.rankL_sum]
  | apart h =>
    exact (d.rankL_fixed hn Δ f a (d.fixed a h) h (d.fixed_get a h)).trans
      (congrArg (fun xs : List (At F A) => 1+(xs.map (fun b => f.rho .left b)).sum)
        (d.fixed_fiber a h)).symm

theorem rankR_fiber (hn : 2 ≤ d.gs.length) (Γ : List (NormalForm P))
    (f : G P Γ F) {A : NormalForm P} (a : At K A) :
    (d.applyR hn Γ f).rho .right a =
      1+(((TraceRoute.full d.route).fiber a).map (fun b => f.rho .right b)).sum := by
  cases At.compare a d.keep with
  | same => rw [d.selected_fiber,d.rankR_keep,d.rankR_sum]
  | apart h =>
    exact (d.rankR_fixed hn Γ f a (d.fixed a h) h (d.fixed_get a h)).trans
      (congrArg (fun xs : List (At F A) => 1+(xs.map (fun b => f.rho .right b)).sum)
        (d.fixed_fiber a h)).symm
end ContractionBlock
end DosenPetric.Reduced.Gentzen
