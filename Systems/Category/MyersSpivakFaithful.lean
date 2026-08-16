/-
Copyright (c) 2026 Shingai Thornton. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Shingai Thornton
-/
import Systems.Category.ShapeSpivak
import Systems.Category.CommonCore
import Mathlib.CategoryTheory.Functor.FullyFaithful

/-!
# The commitments-ladder inclusion is faithful

`myersToSpivak : Paths MyersPosition ⥤ Paths SpivakPosition`
(`ShapeSpivak.lean`) realizes Remark 4.1.2's ladder — Spivak = Myers +
potential + drive — as a functor, and `myersToSpivak_obj_injective` makes it
injective on objects. This file upgrades the inclusion to an **embedding**:
the functor is faithful, so the ladder relationship is structure-preserving
in both directions that matter (objects and hom-sets). Feeds the
seven-traditions-or-eight-embeddings question (issue #40).

The route is the `CommonCore.lean` precedent: Myers's quiver is two arrows
out of `state` with no composable pair, so `Paths MyersPosition` is thin
(`myers_path_subsingleton`), and any functor out of a thin category is
faithful (`faithful_of_subsingleton_hom`).

Provenance: posed 2026-08-15 as the search-shaped arm of the Lea proving-agent
probe (session `qwen38-intake-and-lea-probe`). Neither agent arm closed it at
40 turns; claude-sonnet's run produced the thin-category diagnosis, and the
in-repo `faithful_of_subsingleton_hom` — eight lines from where both agents
searched — finished it. Statement authored upstream; audits to `propext` alone.
-/

open CategoryTheory Quiver

/-- Myers's lens quiver is two arrows out of `state` with no composable pair,
so every hom-set of the free category has at most one element. -/
theorem myers_path_subsingleton (a b : MyersPosition) :
    Subsingleton (Quiver.Path a b) := by
  constructor
  intro p q
  cases p with
  | nil =>
    cases q with
    | nil => rfl
    | cons q' f =>
      cases f with
      | expose => cases q' with | cons q'' g => cases g
      | update => cases q' with | cons q'' g => cases g
  | cons p' e =>
    cases e with
    | expose =>
      cases p' with
      | nil =>
        cases q with
        | cons q' f =>
          cases f with
          | expose => cases q' with | nil => rfl | cons q'' g => cases g
      | cons p'' e' => cases e'
    | update =>
      cases p' with
      | nil =>
        cases q with
        | cons q' f =>
          cases f with
          | update => cases q' with | nil => rfl | cons q'' g => cases g
      | cons p'' e' => cases e'

instance (X Y : Paths MyersPosition) : Subsingleton (X ⟶ Y) :=
  myers_path_subsingleton X Y

/-- **The commitments-ladder inclusion `I_Myers → I_Spivak` is faithful.**
Distinct Myers paths between the same endpoints map to distinct Spivak paths:
the ladder inclusion is an embedding, not merely a functor. -/
theorem myersToSpivak_faithful : myersToSpivak.Faithful :=
  faithful_of_subsingleton_hom _
