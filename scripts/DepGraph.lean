/-
Fast whole-project declaration dependency-graph extractor.

Loads the compiled `Jacobian` environment ONCE and, in a single pass over
`env.constants`, emits one JSON line per project declaration:

  {"n": <name>, "m": <module>, "s": <0|1 direct sorry>,
   "a": <0|1 axiom-clean>, "d": [<direct project dep names>]}

  s = 1  iff the decl's own value/type directly uses `sorryAx`
  a = 1  iff the decl's transitive axiom set ⊆ {propext, Classical.choice, Quot.sound}
          (i.e. "fully proven" — no sorryAx and no introduced axiom)
  d      = direct used-constants restricted to project (Jacobian.*) decls — the edges

This is the "really fast tool": `getUsedConstantsAsSet` is the cheap
reference walk (no re-elaboration), and axiom-cleanliness reuses Lean's
`CollectAxioms`. The Python side (sync-blueprint-db.py) consumes these lines.

Run:  lake env lean --run scripts/DepGraph.lean   > dep-graph.jsonl
-/
-- Import the public-path root rather than the `Jacobian` aggregate: the
-- aggregate olean is often stale (pre-migration header), whereas
-- Jacobian.Solution is the maintained build target and pulls in the whole
-- blueprint-reachable closure. Add more roots here if a blueprint node ever
-- sits outside Solution's import closure.
import Jacobian.Solution
import Lean

open Lean

namespace JacobianDepGraph

/-- Project-internal namespaces. A constant counts as "ours" iff its name
starts with one of these (mirrors blueprint_audit's PROJECT_PREFIXES). -/
def projectPrefixes : List Name := [`JacobianChallenge, `Jacobian]

def isProject (n : Name) : Bool :=
  projectPrefixes.any (fun p => p.isPrefixOf n)

/-- True iff the constant's own type/value directly references `sorryAx`.
This is the CHEAP per-decl fact (no transitive walk); transitive
"depends on sorryAx / an introduced axiom" is computed downstream in Python
over the emitted edge list. -/
def directSorry (ci : ConstantInfo) : Bool :=
  let used := ci.type.getUsedConstants ++ (ci.value?.map Expr.getUsedConstants).getD #[]
  used.contains ``sorryAx

def jsonEscape (s : String) : String :=
  s.foldl (fun acc c =>
    acc ++ (match c with
      | '"'  => "\\\""
      | '\\' => "\\\\"
      | _    => String.singleton c)) ""

/-- Emit one JSON line per project declaration. Runs in `CoreM` so the
public `collectAxioms` (needs `MonadEnv`) is available. -/
def emit : CoreM Unit := do
  let env ← getEnv
  let mut out : String := ""
  for (name, ci) in env.constants.toList do
    -- Skip non-project and internal/compiler-generated constants.
    if !isProject name then continue
    if name.isInternal then continue
    -- Cheap per-decl facts (no transitive walk):
    --   s = 1  the body directly uses `sorryAx`
    --   x = 1  the decl directly references a NON-standard introduced axiom
    --          (sorryAx, or any constant that is itself an `axiom`, excluding
    --          the three standard ones). Python propagates these transitively.
    let s := if directSorry ci then 1 else 0
    let used := ci.getUsedConstantsAsSet
    let mut x := 0
    for c in used.toList do
      if c == ``propext || c == ``Classical.choice || c == ``Quot.sound then
        continue
      match env.find? c with
      | some (.axiomInfo _) => x := 1
      | _ => pure ()
    -- Direct project dependencies (the edges).
    let deps := used.toList.filter (fun d => isProject d && d != name)
    let depsJson := String.intercalate "," (deps.map (fun d => "\"" ++ jsonEscape d.toString ++ "\""))
    out := out ++ "{\"n\":\"" ++ jsonEscape name.toString ++ "\",\"m\":\""
              ++ jsonEscape ((env.getModuleFor? name).getD `unknown).toString ++ "\",\"s\":"
              ++ toString s ++ ",\"x\":" ++ toString x ++ ",\"d\":[" ++ depsJson ++ "]}\n"
  IO.print out

def main : IO Unit := do
  initSearchPath (← findSysroot)
  -- Path-A Montel local-patch-realization leaves sit outside Solution's import
  -- closure (their green providers are not yet consumed downstream), so add them
  -- as extra roots to keep the blueprint node states honest (per the note above).
  -- `MontelGluedMapLocalAgreement` imports `MontelLocalPatchRealization`, so the
  -- latter is reached transitively; both are listed for clarity.
  let env ← importModules
    #[{ module := `Jacobian.Solution },
      { module := `Jacobian.HolomorphicForms.MontelLocalPatchRealization },
      { module := `Jacobian.HolomorphicForms.MontelGluedMapLocalAgreement },
      { module := `Jacobian.HolomorphicForms.MontelForwardSmoothness }] {}
  let coreCtx : Core.Context := { fileName := "DepGraph", fileMap := default }
  let coreState : Core.State := { env }
  let _ ← (emit.run coreCtx coreState).toIO'
  return

end JacobianDepGraph

def main : IO Unit := JacobianDepGraph.main
