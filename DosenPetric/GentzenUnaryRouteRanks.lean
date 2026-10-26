module

public import DosenPetric.GentzenAnchoredRouteFactor

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u
variable {P : Type u}
namespace G

theorem unary_route_rankL {F U Δ : List (NormalForm P)} (g : G P U Δ) (f : G P F Δ)
    (p : Premise g f) (r : Route U F)
    (hb : g.branches=[⟨F,Δ,f,p⟩])
    (hp : ∀ {A : NormalForm P} (a : At F A),p.parent .left a=some (r.get a))
    {C : NormalForm P} (x : At U C) :
    g.rho .left x=1+(((TraceRoute.full r).fiber x).map (fun (a : At F C)=>f.rho .left a)).sum := by
  have he : p.route .left=TraceRoute.full r := by
    apply TraceRoute.ext
    intro A a
    exact (p.route_correct .left a).trans ((hp a).trans (TraceRoute.get_full r a).symm)
  have hx : g.predecessors .left x=
      ((TraceRoute.full r).fiber x).map (fun (a : At F C)=>(⟨⟨F,Δ,f,p⟩,a⟩ : Upper g .left C)) := by
    simp only [predecessors,hb,List.flatMap_cons,List.flatMap_nil,List.append_nil,he]
    rfl
  have hh:=congrArg (fun us : List (Upper g .left C)=>
    1+(us.map (fun a=>a.branch.proof.rho .left a.position)).sum) hx
  exact (g.rho_eq .left x).trans (by simpa only [List.map_map,Function.comp_def] using hh)

theorem unary_route_rankR {F U Δ : List (NormalForm P)} (g : G P Δ U) (f : G P Δ F)
    (p : Premise g f) (r : Route U F)
    (hb : g.branches=[⟨Δ,F,f,p⟩])
    (hp : ∀ {A : NormalForm P} (a : At F A),p.parent .right a=some (r.get a))
    {C : NormalForm P} (x : At U C) :
    g.rho .right x=1+(((TraceRoute.full r).fiber x).map (fun (a : At F C)=>f.rho .right a)).sum := by
  have he : p.route .right=TraceRoute.full r := by
    apply TraceRoute.ext
    intro A a
    exact (p.route_correct .right a).trans ((hp a).trans (TraceRoute.get_full r a).symm)
  have hx : g.predecessors .right x=
      ((TraceRoute.full r).fiber x).map (fun (a : At F C)=>(⟨⟨Δ,F,f,p⟩,a⟩ : Upper g .right C)) := by
    simp only [predecessors,hb,List.flatMap_cons,List.flatMap_nil,List.append_nil,he]
    rfl
  have hh:=congrArg (fun us : List (Upper g .right C)=>
    1+(us.map (fun a=>a.branch.proof.rho .right a.position)).sum) hx
  exact (g.rho_eq .right x).trans (by simpa only [List.map_map,Function.comp_def] using hh)
end G
end DosenPetric.Reduced.Gentzen
