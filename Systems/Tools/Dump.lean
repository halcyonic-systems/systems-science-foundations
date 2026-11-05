import Lean

/-!
# `dump`: the development as data

Walks the compiled environment and writes one JSON file describing every
declaration this project owns: name, kind, module, line range, docstring,
signature, the project-internal declarations it uses, and the axioms its
proof rests on. This is the data a site reads; nothing here proves anything.

Modelled on Mathlib's `scripts/export_crossrefs.lean` (walking an environment
to JSON) and AxiomMath's `lean-metrics` (a dependency graph from
`getUsedConstants`). Auxiliary constants the elaborator generates (`match_`,
`proof_`, recursors, `noConfusion`, equation lemmas) are not nodes; a kept
declaration that uses one inherits what the auxiliary uses, so the graph is
contracted onto the declarations a reader can name, as the Stacks site does
with untagged helper paths. Mathlib is a leaf: its constants are never nodes.

Run: `lake exe dump [out.json] [--no-axioms] [--no-signature] [--no-doc]`
(default `site/data/decls.json`). The JSON is written by hand, one declaration
per line, so a fault in one declaration leaves everything before it on disk.
-/

open Lean Meta

namespace Systems.Tools.Dump

structure Decl where
  name : String
  kind : String
  module : String
  line : Nat
  endLine : Nat
  doc : Option String
  signature : String
  /-- Project declarations this one uses, contracted through auxiliaries. -/
  uses : Array String
  axioms : Array String

structure Flags where
  axioms : Bool := true
  signature : Bool := true
  doc : Bool := true

/-- Modules this project owns: everything under the `Systems` root except this tool. -/
def owned (m : Name) : Bool :=
  (`Systems).isPrefixOf m && !(`Systems.Tools).isPrefixOf m

def moduleOf (env : Environment) (n : Name) : Option Name := do
  let idx ← env.getModuleIdxFor? n
  env.header.moduleNames[idx]?

/-- Suffixes the elaborator appends to structure and inductive declarations. -/
def generatedSuffixes : List String :=
  ["rec", "recOn", "casesOn", "below", "brecOn", "ibelow", "binductionOn",
   "noConfusion", "noConfusionType", "inj", "injEq", "sizeOf_spec", "mk.injEq",
   "mk.sizeOf_spec", "ofNat", "toCtorIdx", "ctorIdx", "ctorElim", "ctorElimType",
   "ofNat_ctorIdx", "congr_simp", "eq_1", "eq_def"]

/-- A constant a reader can name: not private, not elaborator-generated. -/
def isNode (env : Environment) (n : Name) (ci : ConstantInfo) : Bool :=
  !isPrivateName n
  && !n.isInternalDetail
  && !isAuxRecursor env n
  && !isNoConfusion env n
  && !isRecCore env n
  && (match ci with
      | .ctorInfo _ | .recInfo _ | .quotInfo _ => false
      | _ => true)
  && !(generatedSuffixes.any fun s => n.toString.endsWith ("." ++ s))
  -- `brecOn.go` and kin: a generated component anywhere in the name.
  && !(n.toString.splitOn "." |>.any fun c =>
        generatedSuffixes.contains c
        || c.startsWith "match_" || c.startsWith "proof_" || c.startsWith "eq_" || c.startsWith "_")

def kindOf (env : Environment) (n : Name) (ci : ConstantInfo) : MetaM String := do
  if isStructure env n then return (if isClass env n then "class" else "structure")
  match ci with
  | .thmInfo _ => return "theorem"
  | .axiomInfo _ => return "axiom"
  | .inductInfo _ => return "inductive"
  | .opaqueInfo _ => return "opaque"
  | .defnInfo _ =>
    if ← isInstance n then return "instance"
    if env.isProjectionFn n then return "field"
    if (← isProp ci.type) then return "theorem"
    return "def"
  | _ => return "other"

/-- Direct uses, contracted: a non-node project constant is replaced by what it uses. -/
def usesOf (env : Environment) (nodes : NameSet) (n : Name) : Array Name := Id.run do
  let mut out : NameSet := {}
  let mut stack : List Name := (env.find? n).map (·.getUsedConstantsAsSet.toList) |>.getD []
  let mut seen : NameSet := {}
  while h : stack ≠ [] do
    let c := stack.head h
    stack := stack.tail
    if seen.contains c || c == n then continue
    seen := seen.insert c
    match moduleOf env c with
    | some m =>
      if !owned m then continue
      if nodes.contains c then out := out.insert c
      else match env.find? c with
        | some ci => stack := ci.getUsedConstantsAsSet.toList ++ stack
        | none => pure ()
    | none => pure ()
  return out.toArray.qsort (·.toString < ·.toString)

/-- JSON string literal, escaped by hand. -/
def quote (s : String) : String := Id.run do
  let mut out := "\""
  for c in s.toList do
    out := out ++ (match c with
      | '"' => "\\\"" | '\\' => "\\\\" | '\n' => "\\n" | '\r' => "\\r" | '\t' => "\\t"
      | c => if c.val < 0x20 then s!"\\u{String.mk (Nat.toDigits 16 c.val.toNat |>.map id)}" else c.toString)
  return out ++ "\""

def quoteArr (xs : Array String) : String :=
  "[" ++ ",".intercalate (xs.toList.map quote) ++ "]"

def Decl.render (d : Decl) : String :=
  "{" ++ ",".intercalate [
    "\"name\":" ++ quote d.name,
    "\"kind\":" ++ quote d.kind,
    "\"module\":" ++ quote d.module,
    s!"\"line\":{d.line}",
    s!"\"endLine\":{d.endLine}",
    "\"doc\":" ++ (match d.doc with | some s => quote s | none => "null"),
    "\"signature\":" ++ quote d.signature,
    "\"uses\":" ++ quoteArr d.uses,
    "\"axioms\":" ++ quoteArr d.axioms ] ++ "}"

def run (env : Environment) (flags : Flags) (h : IO.FS.Handle)
    (commit date toolchain : String) : MetaM Unit := do
  -- Fold, never `toList`: the map holds all of Mathlib.
  let candidates : Array (Name × ConstantInfo × Name) := env.constants.fold (init := #[]) fun acc n ci =>
    match moduleOf env n with
    | some m => if owned m && isNode env n ci then acc.push (n, ci, m) else acc
    | none => acc
  -- Module list first, so the header is complete before any declaration.
  let mut perModule : Std.HashMap Name Nat := {}
  for (_, _, m) in candidates do perModule := perModule.insert m (perModule.getD m 0 + 1)
  let modules := perModule.toArray.qsort (·.1.toString < ·.1.toString)
  let moduleJson := "[" ++ ",".intercalate (modules.toList.map fun (m, k) =>
    "{\"name\":" ++ quote m.toString ++ ",\"file\":" ++ quote ((m.toString.replace "." "/") ++ ".lean")
      ++ s!",\"declarations\":{k}" ++ "}") ++ "]"
  h.putStr ("{\"project\":\"systems-science-foundations\",\"commit\":" ++ quote commit
    ++ ",\"generatedAt\":" ++ quote date ++ ",\"toolchain\":" ++ quote toolchain
    ++ ",\"modules\":" ++ moduleJson ++ ",\"declarations\":[\n")
  h.flush
  -- Declarations in source order.
  let mut ordered : Array (Name × ConstantInfo × Name × Nat × Nat) := #[]
  -- A node must have a source range; what the elaborator generated has none.
  for (n, ci, m) in candidates do
    if let some r ← findDeclarationRanges? n then
      ordered := ordered.push (n, ci, m, r.range.pos.line, r.range.endPos.line)
  let sorted := ordered.qsort fun a b =>
    a.2.2.1.toString < b.2.2.1.toString || (a.2.2.1 == b.2.2.1 && a.2.2.2.1 < b.2.2.2.1)
  -- The node set is exactly what gets written, so no edge can dangle.
  let mut nodes : NameSet := {}
  for (n, _, _, _, _) in sorted do nodes := nodes.insert n
  let mut first := true
  for (n, ci, m, line, endLine) in sorted do
    let doc ← if flags.doc then findDocString? env n else pure none
    let sig ← if flags.signature then
        tryCatchRuntimeEx
          (do let fmt ← PrettyPrinter.ppSignature n; pure (fmt.fmt.pretty (width := 100)))
          (fun _ => pure n.toString)
      else pure n.toString
    let axioms ← if flags.axioms then collectAxioms n else pure #[]
    let d : Decl := {
      name := n.toString, kind := ← kindOf env n ci, module := m.toString
      line, endLine, doc, signature := sig
      uses := (usesOf env nodes n).map (·.toString)
      axioms := axioms.map (·.toString) |>.qsort (· < ·) }
    h.putStr ((if first then "" else ",\n") ++ d.render)
    first := false
  h.putStr "\n]}\n"
  h.flush
  IO.println s!"{sorted.size} declarations in {modules.size} modules"

end Systems.Tools.Dump

open Systems.Tools.Dump in
unsafe def main (args : List String) : IO UInt32 := do
  let out := (args.filter (!·.startsWith "--")).headD "site/data/decls.json"
  let flags : Flags := {
    axioms := !args.contains "--no-axioms"
    signature := !args.contains "--no-signature"
    doc := !args.contains "--no-doc" }
  let git ← IO.Process.run { cmd := "git", args := #["rev-parse", "HEAD"] }
  let date ← IO.Process.run { cmd := "date", args := #["-u", "+%Y-%m-%dT%H:%M:%SZ"] }
  let toolchain ← IO.FS.readFile "lean-toolchain"
  initSearchPath (← findSysroot)
  enableInitializersExecution
  if let some dir := (System.FilePath.mk out).parent then IO.FS.createDirAll dir
  let h ← IO.FS.Handle.mk out .write
  -- `loadExts`: without the extension entries no app unexpander fires and
  -- every signature prints as `Iff a b`; `withImportModules` never loads them.
  let env ← importModules #[{ module := `Systems }] {} (loadExts := true)
  let _ ← (run env flags h git.trimAscii.toString date.trimAscii.toString toolchain.trimAscii.toString).toIO
    { fileName := "<dump>", fileMap := default, maxHeartbeats := 0 } { env }
  return 0
