import Lean

/-!
# `@[atlas "entry-id"]`: the bridge to the atlas

The atlas at math.systems catalogues formal definitions of "system", one entry
per passage, each with a permanent id such as `klir-2001-eq-1-1`
(`https://w3id.org/mathematical-systems/atlas/entry/<id>`). A declaration
here that is an entry's formal counterpart carries that id:

```lean
@[atlas "klir-2001-eq-1-1"]
abbrev KlirShape := Paths KlirPosition
```

The tag is narrow by decision (Shingai, 2026-11-05): it marks the declaration
that *is* the definition's counterpart, one or two per entry, never
everything that belongs to a tradition. Which declarations belong to a
tradition is a mechanical reading of module and namespace names, made by the
site, not asserted here.

The tags are read back by `lake exe dump` (`Systems/Tools/Dump.lean`) into the
site's data, replacing the hand-kept `formalisedAs` pointers in the atlas's
entry files and the regex parser that resolved them. `#atlas_tags` lists them.

Pattern: Mathlib's `Mathlib/Tactic/CrossRefAttribute.lean` (`@[stacks TAG]`),
reduced to one database.
-/

open Lean Elab Command

namespace Systems.Atlas

/-- One tag: a declaration and the atlas entry it formalises. -/
structure Tag where
  declName : Name
  id : String
  comment : String
  deriving Inhabited, Repr, BEq

initialize tagExt : SimplePersistentEnvExtension Tag (Array Tag) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := (·.push ·)
    addImportedFn := fun as => as.flatten
  }

/-- Every tag in scope, imported and local. -/
def tags (env : Environment) : Array Tag := tagExt.getState env

/-- An atlas entry id: lowercase letters, digits and hyphens, as the w3id namespace mints them. -/
def validId (s : String) : Bool :=
  !s.isEmpty && s.all (fun c => c.isLower || c.isDigit || c == '-') && !s.startsWith "-" && !s.endsWith "-"

syntax (name := atlasAttr) "atlas " str (ppSpace str)? : attr

initialize registerBuiltinAttribute {
  name := `atlasAttr
  descr := "the math.systems atlas entry this declaration formalises"
  add := fun declName stx _ => do
    match stx with
    | `(attr| atlas $id:str $[$comment:str]?) =>
      let idStr := id.getString
      unless validId idStr do
        throwError "atlas id must be lowercase letters, digits and hyphens, got {idStr}"
      modifyEnv fun env => tagExt.addEntry env
        { declName, id := idStr, comment := (comment.map (·.getString)).getD "" }
    | _ => throwUnsupportedSyntax
}

/-- List every atlas tag in scope: `entry-id ← declaration`. -/
elab "#atlas_tags" : command => do
  let ts := tags (← getEnv)
  if ts.isEmpty then logInfo "no atlas tags in scope"
  for t in ts.qsort (·.id < ·.id) do
    logInfo m!"{t.id} ← {t.declName}{if t.comment.isEmpty then "" else s!"  ({t.comment})"}"

end Systems.Atlas
