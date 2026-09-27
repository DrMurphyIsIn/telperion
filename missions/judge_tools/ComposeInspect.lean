/-  ComposeInspect.lean -- facts about ONE judged theorem, for the compositional judge
    (telperion.missions.compose; missions-comparator-heavy.yml).

    Run inside a judge bundle, after the Comparator has passed on the same built modules:

        lake env lean --run ComposeInspect.lean <Module> <Theorem>

    Prints one JSON object:
      theorem          the constant inspected (must be a theorem)
      type_const       its type when that type is a bare constant (`AllZeros_h1000.BandHyp`), else ""
      binders          the leading Π-binder types that are bare constants, in order, stopping at the
                       first that is not (for the implication: the eight band hypotheses, then `Complex`)
      axioms           the axioms in its dependency closure (sorted)
      closure_size     number of constants in that closure
      closure_modules  the module that declares each closure constant (sorted, unique)

    The dependency closure is the kernel's: a constant's type and value, an inductive's
    constructors and mutual block, a constructor's inductive, a recursor's rules -- the same
    set `lean4export <Module> -- <Theorem>` exports for the Comparator to replay. Module
    attribution is exact (`Environment.getModuleIdxFor?`), which is what lets the judge assert
    that the implication's closure contains NO certificate module.
-/
import Lean

open Lean

def usedBy (ci : ConstantInfo) : Array Name := Id.run do
  let mut out := ci.type.getUsedConstants
  if let some v := ci.value? (allowOpaque := true) then
    out := out ++ v.getUsedConstants
  match ci with
  | .inductInfo v => out := out ++ v.ctors.toArray ++ v.all.toArray
  | .ctorInfo v => out := out.push v.induct
  | .recInfo v =>
    out := out ++ v.all.toArray
    for r in v.rules do
      out := out ++ r.rhs.getUsedConstants
  | _ => pure ()
  return out

partial def closureOf (env : Environment) (root : Name) : Except String NameSet := do
  let mut seen : NameSet := {}
  let mut work : Array Name := #[root]
  while !work.isEmpty do
    let n := work.back!
    work := work.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | throw s!"constant {n} is referenced but not in the environment"
    for m in usedBy ci do
      if !seen.contains m then work := work.push m
  return seen

partial def constBinders (e : Expr) (acc : Array String) : Array String :=
  match e with
  | .forallE _ t b _ =>
    if t.isConst && t.constLevels!.isEmpty then constBinders b (acc.push t.constName!.toString)
    else acc
  | _ => acc

def main (args : List String) : IO UInt32 := do
  let [modStr, thmStr] := args
    | IO.eprintln "usage: lake env lean --run ComposeInspect.lean <Module> <Theorem>"; return 2
  let modName := modStr.toName
  let thm := thmStr.toName
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := modName }] {} (trustLevel := 1024) (loadExts := false)
  let some ci := env.find? thm
    | IO.eprintln s!"{thm} is not declared in (the closure of) {modName}"; return 1
  unless ci matches .thmInfo _ do
    IO.eprintln s!"{thm} is not a theorem"; return 1
  let clo ← match closureOf env thm with
    | .ok s => pure s
    | .error e => IO.eprintln e; return 1
  let mut axioms : Array String := #[]
  let mut mods : Std.HashSet String := {}
  for n in clo do
    if let some (.axiomInfo _) := env.find? n then axioms := axioms.push n.toString
    match env.getModuleIdxFor? n with
    | some idx => mods := mods.insert (env.header.moduleNames[idx.toNat]!).toString
    | none => mods := mods.insert modStr
  let ty := ci.type
  let tyConst := if ty.isConst && ty.constLevels!.isEmpty then ty.constName!.toString else ""
  let out := Json.mkObj [
    ("theorem", toJson thm.toString),
    ("type_const", toJson tyConst),
    ("binders", toJson (constBinders ty #[])),
    ("axioms", toJson (axioms.qsort (· < ·))),
    ("closure_size", toJson clo.size),
    ("closure_modules", toJson (mods.toArray.qsort (· < ·)))
  ]
  IO.println out.compress
  return 0
