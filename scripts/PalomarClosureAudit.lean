module

import Lean
import LeanExport.Parse
import Lake.Check.Compare
import Lake.Check.Util

open Lean

private def selected : Array Name := #[
  `DosenPetric.Palomar.maximality, `DosenPetric.Palomar.short_maximality,
  `DosenPetric.Palomar.congruence_dichotomy, `DosenPetric.Palomar.identity_ne_zero,
  `DosenPetric.Palomar.no_top_to_bot]

private def kind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

/-- Canonicalize bound universe parameter names, preserving their order and arity.
Compiler-generated hygiene names contain the source module identity. -/
private def alphaUniverses (i : ConstantInfo) : ConstantInfo :=
  let ps := (List.range i.levelParams.length).map (Name.num `_palomarUniverse)
  let e := fun e : Expr => e.instantiateLevelParams i.levelParams (ps.map Level.param)
  match i with
  | .axiomInfo x => .axiomInfo { x with levelParams := ps, type := e x.type }
  | .defnInfo x => .defnInfo { x with levelParams := ps, type := e x.type, value := e x.value }
  | .thmInfo x => .thmInfo { x with levelParams := ps, type := e x.type, value := e x.value }
  | .opaqueInfo x => .opaqueInfo { x with levelParams := ps, type := e x.type, value := e x.value }
  | .quotInfo x => .quotInfo { x with levelParams := ps, type := e x.type }
  | .inductInfo x => .inductInfo { x with levelParams := ps, type := e x.type }
  | .ctorInfo x => .ctorInfo { x with levelParams := ps, type := e x.type }
  | .recInfo x => .recInfo { x with levelParams := ps, type := e x.type, rules := x.rules.map (fun r => { r with rhs := e r.rhs }) }

private def used (i : ConstantInfo) : Array Name :=
  ((Lake.Check.runForUsedConsts (m := StateM (Array Name)) i
    (fun n => modify (fun a => a.push n))).run #[]).2

private def closure (env : LeanExport.ExportedEnv) (root : Name) : Except String (Array Name) := do
  let mut pending := #[root]
  let mut seen : NameHashSet := {}
  let mut result := #[]
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    if !seen.contains n then
      let some info := env.constMap[n]? | throw s!"Missing closure constant {n}"
      seen := seen.insert n
      result := result.push n
      pending := pending ++ used info
  return result.qsort (fun a b => a.toString < b.toString)

public def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  match args with
  | ["names", mod, dest] =>
    let env ← importModules #[{ module := mod.toName }] {}
    let names := env.constants.toList.filterMap fun (n, c) =>
      if (`DosenPetric).isPrefixOf n then
        some (n.toString, kind c)
      else none
    let names := names.toArray.qsort (fun a b => a.1 < b.1)
    IO.FS.writeFile dest <| (toJson names).compress ++ "\n"
    IO.println s!"PASS: enumerated {names.size} presentation declarations"
  | ["compare", challenge, solution, namesFile, dest] =>
    let cc ← LeanExport.parseStream <| .ofHandle (← IO.FS.Handle.mk challenge .read)
    let sc ← LeanExport.parseStream <| .ofHandle (← IO.FS.Handle.mk solution .read)
    let names : Array (String × String) ← IO.ofExcept <|
      (Json.parse (← IO.FS.readFile namesFile)).bind fromJson?
    let allNames := names.map (fun p => p.1.toName)
    -- The public Comparator is run separately on the unmodified exports.
    -- This additional comparison also seeds every generated declaration.
    -- Its sole alpha-conversion removes module-qualified bound universe names.
    let normalize := fun env : LeanExport.ExportedEnv =>
      { env with constMap := env.constMap.map (fun _ c => alphaUniverses c) }
    IO.ofExcept <| Lake.Check.compareAt (normalize cc) (normalize sc) selected #[]
      (allNames.filter (fun n => !selected.contains n))
    let renamed := allNames.filter fun n =>
      match cc.constMap[n]?, sc.constMap[n]? with
      | some c, some d => c.levelParams != d.levelParams
      | _, _ => false
    let mut dependencyReports := #[]
    for n in selected do
      let deps ← IO.ofExcept <| closure sc n
      let axioms := deps.filter fun a =>
        match sc.constMap[a]? with | some (.axiomInfo _) => true | _ => false
      unless axioms.all (fun a => #[`propext, `Quot.sound, `Classical.choice].contains a) do
        throw <| IO.userError s!"Unpermitted transitive axiom in {n}: {axioms}"
      if n == `DosenPetric.Palomar.short_maximality then
        for needed in #[`DosenPetric.Presentation.ShortProof.total,
            `DosenPetric.Isolation.normalized_literal_context,
            `DosenPetric.ContextualCollapse.all_contexts] do
          unless deps.contains needed do
            throw <| IO.userError s!"Short proof route lacks {needed}"
        for forbidden in #[`DosenPetric.Palomar.maximality,
            `DosenPetric.relative_maximality,
            `DosenPetric.Presentation.fragment_maximality,
            `DosenPetric.Presentation.fragment_dichotomy,
            `DosenPetric.Presentation.ProofCongruence.of_closed_fragment,
            `DosenPetric.Palomar.PrimitiveCongruence.full] do
          if deps.contains forbidden then
            throw <| IO.userError s!"Short proof unexpectedly depends on {forbidden}"
      if n == `DosenPetric.Palomar.maximality then
        unless deps.contains `DosenPetric.relative_maximality do
          throw <| IO.userError "Fold proof does not reach actual relative_maximality"
      dependencyReports := dependencyReports.push <| Json.mkObj [
        ("theorem", toJson n.toString), ("declaration_count", toJson deps.size),
        ("axioms", toJson (axioms.map Name.toString)),
        ("complete_dependencies", toJson (deps.map Name.toString))]
    let report := Json.mkObj [
      ("status", "pass"), ("selected_types", toJson selected.size),
      ("concrete_declarations", toJson (allNames.size - selected.size)),
      ("method", "SDK compareAt with every non-selected presentation constant as an exact-value seed"),
      ("universe_parameters", "arity, order and all uses compared after alpha-renaming bound universe names"),
      ("alpha_renamed_declarations", toJson (renamed.map Name.toString)),
      ("proof_dependencies", Json.arr dependencyReports),
      ("constructors_and_recursors", "types, indices, fields and reduction rules compared"),
      ("definition_and_theorem_values", "compared except the five selected proof values"),
      ("transitive_closure", "all type and relevant value dependencies followed by SDK"),
      ("declarations", toJson names)]
    IO.FS.writeFile dest (report.pretty ++ "\n")
    IO.println s!"PASS: types and complete values modulo bound-universe alpha-renaming for {allNames.size - selected.size} concrete declarations; {selected.size} selected types"
  | _ => throw <| IO.userError "Usage: names MODULE OUTPUT | compare CHALLENGE_EXPORT SOLUTION_EXPORT NAMES OUTPUT"
