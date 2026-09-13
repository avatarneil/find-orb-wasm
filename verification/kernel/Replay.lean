import Lean
import RawReplay

/-! GPL-2.0-or-later. Recheck theorem dependency closures in an EMPTY kernel
environment. Imported .olean declarations are data, not trusted proof results.
The three permitted foundational axioms are reported; unsafe/partial constants
and all other axioms fail. Lean's replay also reconstructs/checks inductives,
constructors, and recursors. --corrupt is a required negative control.
-/

open Lean

def permittedAxiom (n : Name) : Bool :=
  [``propext, ``Classical.choice, ``Quot.sound].contains n

def sameSignature (a b : ConstantInfo) : Bool :=
  a.name == b.name && a.levelParams == b.levelParams && a.type.equal b.type

def validateAxiom (canonical : Environment) (ci : ConstantInfo) : IO Unit := do
  if ci matches .axiomInfo _ then
    if !permittedAxiom ci.name then throw <| IO.userError s!"Forbidden axiom: {ci.name}"
    let some (.axiomInfo expected) := canonical.find? ci.name |
      throw <| IO.userError s!"Canonical core axiom absent: {ci.name}"
    if !sameSignature ci (.axiomInfo expected) then
      throw <| IO.userError s!"Canonical axiom signature mismatch: {ci.name}"

def validatePrimitive (canonical source : Environment) (name : Name) : IO Unit := do
  let some expected := canonical.find? name | throw <| IO.userError s!"Canonical primitive absent: {name}"
  let some actual := source.find? name | throw <| IO.userError s!"Source primitive absent: {name}"
  let shape := match actual, expected with
    | .inductInfo a, .inductInfo b =>
      a.numParams == b.numParams && a.numIndices == b.numIndices && a.all == b.all &&
      a.ctors == b.ctors && a.numNested == b.numNested && a.isRec == b.isRec &&
      a.isUnsafe == b.isUnsafe && a.isReflexive == b.isReflexive
    | .ctorInfo a, .ctorInfo b => a == b
    | .recInfo a, .recInfo b => a == b
    | .quotInfo a, .quotInfo b => match a.kind, b.kind with
      | .type, .type | .ctor, .ctor | .lift, .lift | .ind, .ind => true
      | _, _ => false
    | _, _ => false
  if !sameSignature actual expected || !shape then
    throw <| IO.userError s!"Canonical primitive shape mismatch: {name}"

partial def collect (source canonical : Environment) (name : Name)
    (seen : Std.HashMap Name ConstantInfo) : IO (Std.HashMap Name ConstantInfo) := do
  if seen.contains name then return seen
  let some ci := source.find? name | throw <| IO.userError s!"Missing declaration: {name}"
  if ci.isUnsafe || ci.isPartial then
    throw <| IO.userError s!"Unsafe or partial dependency: {name}"
  validateAxiom canonical ci
  let mut result := seen.insert name ci
  for dep in ci.getUsedConstantsAsSet do
    result ← collect source canonical dep result
  match ci with
  | .inductInfo info =>
    for dep in info.all ++ info.ctors do result ← collect source canonical dep result
  | .ctorInfo info => result ← collect source canonical info.induct result
  | .recInfo info =>
    for dep in info.all do result ← collect source canonical dep result
  | _ => pure ()
  return result

def main (args : List String) : IO Unit := do
  let sysroot ← findSysroot
  initSearchPath sysroot
  let userSearch ← searchPathRef.get
  -- Load the reference signatures exclusively from the verified release.
  -- initSearchPath alone would prepend LEAN_PATH and allow module shadowing.
  let corePath ← getLibDir sysroot
  let canonical ← try
    searchPathRef.set [corePath]
    importModules #[{module := `Init}] {} 0 (loadExts := false)
  finally
    searchPathRef.set userSearch
  let corrupt := args.contains "--corrupt"
  let forgeAxiom := args.contains "--forge-axiom"
  let args := args.filter fun s => s != "--corrupt" && s != "--forge-axiom"
  let moduleName :: theoremNames := args |
    throw <| IO.userError "Usage: Replay.lean [--corrupt] MODULE THEOREM..."
  if theoremNames.isEmpty then throw <| IO.userError "At least one theorem is required"
  let source ← importModules #[{module := moduleName.toName}] {} 0 (loadExts := false)
  let primitives := [``Eq, ``Eq.refl, ``Eq.rec, ``Quot, ``Quot.mk, ``Quot.lift, ``Quot.ind]
  for name in primitives do validatePrimitive canonical source name
  let mut constants : Std.HashMap Name ConstantInfo := {}
  for s in theoremNames do
    let name := s.toName
    match source.find? name with
    | some (.thmInfo _) => pure ()
    | _ => throw <| IO.userError s!"Required theorem is absent or not a theorem: {name}"
    constants ← collect source canonical name constants
  let axioms := constants.toList.filterMap fun (n, ci) =>
    match ci with | .axiomInfo _ => some n.toString | _ => none
  if corrupt then
    let name := theoremNames.head!.toName
    match constants[name]? with
    | some (.thmInfo info) =>
      constants := constants.insert name (.thmInfo {info with value := mkConst ``True.intro})
    | _ => throw <| IO.userError "Corruption target absent"
  if forgeAxiom then
    match constants[``propext]? with
    | some (.axiomInfo info) =>
      constants := constants.insert ``propext (.axiomInfo {info with type := mkConst ``False})
    | _ => throw <| IO.userError "Forgery target absent"
  -- Repeat after negative-control mutations; no allowed-name axiom may bypass
  -- the signature gate between collection and kernel insertion.
  for (_, ci) in constants.toList do validateAxiom canonical ci
  let empty := (← mkEmptyEnvironment 0).toKernelEnv
  -- Quot, Quot.mk, Quot.lift, and Quot.ind form one atomic kernel primitive.
  -- Lean 4.24's replay helper otherwise submits quotDecl once per quotInfo,
  -- causing duplicate-declaration panics (which the runtime can log and recover
  -- from). Recheck Eq first, initialize this primitive ONCE in the kernel, then
  -- exclude all declarations the primitive itself generated from the replay.
  let eqConstants ← collect canonical canonical ``Eq {}
  let eqChecked ← RawKernelReplay.replay eqConstants empty
  let base ← match eqChecked.addDeclCore 0 .quotDecl (cancelTk? := none) with
    | .ok env => pure env
    | .error ex => throw <| IO.userError <| (← ex.toMessageData {} |>.toString)
  let remaining := constants.filter fun n _ => (base.find? n).isNone
  let checked ← RawKernelReplay.replay remaining base
  for s in theoremNames do
    if (checked.find? s.toName).isNone then throw <| IO.userError s!"Theorem not replayed: {s}"
  let signatures ← (primitives ++ [``propext, ``Classical.choice, ``Quot.sound]).mapM fun name => do
    let some ci := canonical.find? name | throw <| IO.userError s!"Canonical signature absent: {name}"
    pure <| Json.mkObj [("name", toJson name.toString),
      ("levelParams", toJson (ci.levelParams.map Name.toString)), ("type", toJson ci.type.dbgToString)]
  IO.println <| Json.compress <| Json.mkObj [
    ("module", toJson moduleName), ("theorems", toJson theoremNames),
    ("replayedDeclarations", toJson constants.size), ("axioms", toJson axioms),
    ("emptyInitialEnvironment", toJson true),
    ("primitiveInitialization", toJson "Eq rechecked; atomic kernel quotDecl initialized once"),
    ("canonicalCorePath", toJson corePath.toString),
    ("canonicalSignaturesValidated", toJson true), ("canonicalSignatures", toJson signatures),
    ("forgedAxiom", toJson forgeAxiom),
    ("corrupt", toJson corrupt),
    ("passed", toJson true)]
