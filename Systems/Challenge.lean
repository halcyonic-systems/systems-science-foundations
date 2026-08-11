/-
Copyright (c) 2026 Shingai Thornton. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Shingai Thornton
-/
import Systems.Category.CommonCore
import Systems.Category.SharedPrimitive

/-!
# Challenge: the K ≅ 2 headline claims, restated for cold verification

This file is a trusted statement file in the comparator style
(leanprover/comparator; the pattern behind anthropics/zeta-23-lean and
openai/ten-proofs). It restates every headline theorem of the K ≅ 2 result
with its full type written out, and assigns the library proof to it. If this
file elaborates, each library theorem proves *exactly* the statement written
here; `lake build` replays everything through the kernel.

A cold reader verifies the result by reading THIS file plus the definitions it
references — never the proofs:

* the eight position quivers (`Systems/Category/Shape*.lean`) — one inductive
  vertex type and one inductive arrow type each, transcribed from the eight
  traditions' texts;
* the eight embedding prefunctors `klirTo*Pre` and their lifts `klirTo*`
  (`CommonCore.lean`, `ShapeWillems.lean`);
* `SharedPrimitive.QuiverEmbedding` (injective-on-vertices, injective-on-edges),
  `SharedPrimitive.Zigzag` (undirected connectivity), and the fork quiver
  `SharedPrimitive.VPos`/`VArrow` used in the counterexample.

Check with `scripts/check-challenge.sh`: builds this module and verifies every
theorem below depends only on Lean's three standard axioms
(`propext`, `Classical.choice`, `Quot.sound`).

What is claimed, and what is not:

* **Existence** (`*_obj_injective`, `*_faithful`): eight embeddings of `I_Klir`
  into the eight tradition shape categories, injective on objects and faithful.
  Faithfulness is inherited from `I_Klir` being thin; the content is object
  injectivity.
* **Repaired maximality** (`connected_is_single_arrow`): quiver-level and
  relative to the encoded presentations — a connected quiver embedding into
  both the Joslyn and Willems shapes with at least one edge is exactly one
  arrow. NOT a free-category maximality claim.
* **The refutation** (`free_category_maximality_fails`, `v_has_three_objects`):
  the free-category maximality claim is FALSE — a three-object fork embeds
  into all eight free categories injectively and faithfully. Kept on the
  record deliberately.
-/

open CategoryTheory

namespace Challenge

/-! ## Existence: object injectivity (the content) -/

theorem klirToBunge_obj_injective : Function.Injective klirToBungePre.obj :=
  _root_.klirToBunge_obj_injective

theorem klirToMobus_obj_injective : Function.Injective klirToMobusPre.obj :=
  _root_.klirToMobus_obj_injective

theorem klirToMyers_obj_injective : Function.Injective klirToMyersPre.obj :=
  _root_.klirToMyers_obj_injective

theorem klirToWymore_obj_injective : Function.Injective klirToWymorePre.obj :=
  _root_.klirToWymore_obj_injective

theorem klirToMesarovic_obj_injective : Function.Injective klirToMesarovicPre.obj :=
  _root_.klirToMesarovic_obj_injective

theorem klirToJoslyn_obj_injective : Function.Injective klirToJoslynPre.obj :=
  _root_.klirToJoslyn_obj_injective

theorem klirToSpivak_obj_injective : Function.Injective klirToSpivakPre.obj :=
  _root_.klirToSpivak_obj_injective

theorem klirToWillems_obj_injective : Function.Injective klirToWillemsPre.obj :=
  _root_.klirToWillems_obj_injective

/-! ## Existence: faithfulness (inherited from I_Klir being thin) -/

theorem klirToBunge_faithful : klirToBunge.Faithful := _root_.klirToBunge_faithful
theorem klirToMobus_faithful : klirToMobus.Faithful := _root_.klirToMobus_faithful
theorem klirToMyers_faithful : klirToMyers.Faithful := _root_.klirToMyers_faithful
theorem klirToWymore_faithful : klirToWymore.Faithful := _root_.klirToWymore_faithful
theorem klirToMesarovic_faithful : klirToMesarovic.Faithful :=
  _root_.klirToMesarovic_faithful
theorem klirToJoslyn_faithful : klirToJoslyn.Faithful := _root_.klirToJoslyn_faithful
theorem klirToSpivak_faithful : klirToSpivak.Faithful := _root_.klirToSpivak_faithful
theorem klirToWillems_faithful : klirToWillems.Faithful := _root_.klirToWillems_faithful

/-! ## Repaired maximality: quiver-level, forced by Joslyn and Willems -/

theorem connected_is_single_arrow {V : Type*} [Quiver V]
    (eJ : SharedPrimitive.QuiverEmbedding V JoslynPosition)
    (eW : SharedPrimitive.QuiverEmbedding V WillemsPosition)
    (conn : ∀ a b : V, SharedPrimitive.Zigzag a b) {x y : V} (e : x ⟶ y) :
    x ≠ y ∧ (∀ w : V, w = x ∨ w = y) ∧ ∀ (u v : V) (_ : u ⟶ v), u = x ∧ v = y :=
  SharedPrimitive.connected_is_single_arrow eJ eW conn e

/-- `I_Klir` itself has exactly two positions (pigeonhole form). -/
theorem klir_has_two_elements :
    ∀ (f : Fin 3 → KlirPosition), ¬ Function.Injective f :=
  _root_.klir_has_two_elements

/-! ## The refutation, kept on the record -/

theorem free_category_maximality_fails :
    Function.Injective SharedPrimitive.vToBungePre.obj ∧
      (Paths.lift SharedPrimitive.vToBungePre).Faithful ∧
    Function.Injective SharedPrimitive.vToMobusPre.obj ∧
      (Paths.lift SharedPrimitive.vToMobusPre).Faithful ∧
    Function.Injective SharedPrimitive.vToMyersPre.obj ∧
      (Paths.lift SharedPrimitive.vToMyersPre).Faithful ∧
    Function.Injective SharedPrimitive.vToWymorePre.obj ∧
      (Paths.lift SharedPrimitive.vToWymorePre).Faithful ∧
    Function.Injective SharedPrimitive.vToMesarovicPre.obj ∧
      (Paths.lift SharedPrimitive.vToMesarovicPre).Faithful ∧
    Function.Injective SharedPrimitive.vToSpivakPre.obj ∧
      (Paths.lift SharedPrimitive.vToSpivakPre).Faithful ∧
    Function.Injective SharedPrimitive.vToWillemsPre.obj ∧
      (Paths.lift SharedPrimitive.vToWillemsPre).Faithful ∧
    Function.Injective SharedPrimitive.vToJoslynPre.obj ∧
      (Paths.lift SharedPrimitive.vToJoslynPre).Faithful :=
  SharedPrimitive.free_category_maximality_fails

/-- The fork is strictly larger than `I_Klir`: three objects, not two. -/
theorem v_has_three_objects :
    ∀ (f : SharedPrimitive.VPos → KlirPosition), ¬ Function.Injective f :=
  SharedPrimitive.v_has_three_objects

end Challenge

/-! ## Axiom audit — read by scripts/check-challenge.sh -/

#print axioms Challenge.klirToBunge_obj_injective
#print axioms Challenge.klirToMobus_obj_injective
#print axioms Challenge.klirToMyers_obj_injective
#print axioms Challenge.klirToWymore_obj_injective
#print axioms Challenge.klirToMesarovic_obj_injective
#print axioms Challenge.klirToJoslyn_obj_injective
#print axioms Challenge.klirToSpivak_obj_injective
#print axioms Challenge.klirToWillems_obj_injective
#print axioms Challenge.klirToBunge_faithful
#print axioms Challenge.klirToMobus_faithful
#print axioms Challenge.klirToMyers_faithful
#print axioms Challenge.klirToWymore_faithful
#print axioms Challenge.klirToMesarovic_faithful
#print axioms Challenge.klirToJoslyn_faithful
#print axioms Challenge.klirToSpivak_faithful
#print axioms Challenge.klirToWillems_faithful
#print axioms Challenge.connected_is_single_arrow
#print axioms Challenge.klir_has_two_elements
#print axioms Challenge.free_category_maximality_fails
#print axioms Challenge.v_has_three_objects
