/-
Copyright (c) 2026 Shingai Thornton. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Shingai Thornton
-/
import Systems.Category.CommonCore

/-!
# The Shared Primitive Is a Single Arrow

This file replaces the old "maximality of the common core" claim, which was false.

## What went wrong

The retired statement was: *`I_Klir` is the largest connected category admitting a
faithful functor into every `I_X`.* Two defects.

1. Faithfulness constrains hom-sets, not objects, so it cannot support "largest".
   The three-object chain is thin and connected and maps faithfully into `2`.
   Strengthening to *faithful and injective on objects* fixes this.

2. It is still false after that fix. Let `V` be the quiver with one source and two
   arrows to two distinct sinks. `V` is connected, has three objects and two arrows,
   and embeds injectively-on-objects and faithfully into all eight shape categories:

   | Target | source ↦ | sinks ↦ |
   |---|---|---|
   | Bunge | `structure'` | `composition`, `environment` |
   | Mobus | `externalFlows` | `environment`, `boundary` |
   | Myers | `state` | `output`, `input` |
   | Wymore | `state` | `input`, `output` |
   | Mesarovic | `globalState` | `input`, `output` |
   | Spivak | `parameter` | `output`, `input` |
   | Willems | `behavior` | `signal`, `time` |
   | Joslyn | `controller` | `effector`, `controlled` |

   The Joslyn row is the leak. There is no *arrow* `controller ⟶ controlled`, but
   there is a *path* (`disturbance ≫ efferent`), and in the free category on a
   quiver every path is a morphism. So a competitor can enter through a derived
   composite that the tradition never asserted.

## The level at which the claim is true

Compare the generating quivers, not their free categories. An embedding is then a
prefunctor injective on vertices that sends **edges to edges** and is injective on
each edge set. Derived composites stop counting, and `V` dies immediately: no vertex
of the Joslyn quiver has two outgoing edges.

This is not a retreat from category theory. `Paths` is left adjoint to the forgetful
functor `Cat ⥤ Quiv`, so the two levels are formally related; the choice is which
side of that adjunction carries the comparison. The quiver side is where a tradition's
*asserted* primitives live. The category side is where their *consequences* live. The
existence half of the convergence result was already quiver-level and was merely
stated more weakly than it was proven: every `klirTo*Pre` sends Klir's one arrow to a
single generating arrow of the target, never to a composite.

## The result

Two traditions do all the work, and the remaining six are not needed:

- **Joslyn** has no vertex of out-degree two, which kills the fork `x → y`, `x → z`.
- **Willems** has no vertex of in-degree two, which kills the cofork `x → z ← y`,
  and no composable pair of edges, which kills the two-chain `x → y → z`, every
  self-loop, and every antiparallel pair.
- Willems also has no parallel edges, which with edge-injectivity kills those too.

Together: in any quiver embedding into both, two edges either coincide or share no
vertex at all (`edges_coincide_or_disjoint`). Adding weak connectivity closes it —
nothing outside `{x, y}` is reachable from `x` once `x ⟶ y` is an edge
(`zigzag_confined`), so the quiver has exactly two vertices and exactly one edge
(`connected_is_single_arrow`). That quiver is `I_Klir`, whose free category is the
walking arrow **2**.

The reading is not "K is maximal" but: **the only dependency all eight traditions
directly assert is one.** That the cybernetic shape (Joslyn) and the behavioural
shape (Willems) are jointly what force it is the substantive content. Willems is
therefore not the decorative "kernel-neutrality witness" the `CommonCore` header
calls it; it is load-bearing here.

## Honest limits

**This theorem is relative to the presentations.** Quiver-level claims are not
invariant under adding derived arrows, unlike free-category ones. Drawing Joslyn with
an additional `controller ⟶ controlled` edge, which one could argue for, would let
`V` back in and the result would fail. The defence is that each edge is a documented
primitive commitment of its source text; see `docs/language/terminology-concordance.md`
for the per-cell citations. This is a claim about what the literature asserts, and
sensitivity to how each tradition states itself is the subject matter rather than a
defect. It should be disclosed, not buried.

**No remaining gap.** The theorem is complete over an arbitrary vertex type, with
connectivity given by `Zigzag`. Note what is *not* assumed: no finiteness, no
decidable equality, no bound on the number of vertices or edges.
-/

open CategoryTheory

namespace SharedPrimitive

/-- An embedding of quivers: injective on vertices, edges to edges, injective on
each edge set. This is the subcategory-inclusion notion transposed to `Quiv`. -/
structure QuiverEmbedding (V W : Type*) [Quiver V] [Quiver W] where
  toPre : Prefunctor V W
  obj_inj : Function.Injective toPre.obj
  map_inj : ∀ {x y : V}, Function.Injective (toPre.map : (x ⟶ y) → _)

-- ═══════════════════════════════════════════════════════════════════════════════
-- § Obstructions in the two load-bearing shapes
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Every vertex of the Joslyn quiver has out-degree at most one. -/
theorem joslyn_out_degree_le_one {a b c : JoslynPosition} (e : a ⟶ b) (f : a ⟶ c) :
    b = c := by
  cases e <;> cases f <;> rfl

/-- Every vertex of the Willems quiver has in-degree at most one. -/
theorem willems_in_degree_le_one {a b c : WillemsPosition} (e : a ⟶ c) (f : b ⟶ c) :
    a = b := by
  cases e <;> cases f <;> rfl

/-- No two edges of the Willems quiver compose: both edges leave `behavior`, and
`signal` and `time` are sinks. -/
theorem willems_no_composable {a b c : WillemsPosition} (e : a ⟶ b) (f : b ⟶ c) :
    False := by
  cases e <;> cases f

/-- The Willems quiver has no parallel edges. -/
theorem willems_no_parallel {a b : WillemsPosition} (e f : a ⟶ b) : e = f := by
  cases e <;> cases f <;> rfl

-- ═══════════════════════════════════════════════════════════════════════════════
-- § Transfer to an arbitrary quiver
-- ═══════════════════════════════════════════════════════════════════════════════

variable {V : Type*} [Quiver V]

/-- No fork. Two edges out of a common source have the same target. -/
theorem no_fork (eJ : QuiverEmbedding V JoslynPosition) {x y z : V}
    (e : x ⟶ y) (f : x ⟶ z) : y = z :=
  eJ.obj_inj (joslyn_out_degree_le_one (eJ.toPre.map e) (eJ.toPre.map f))

/-- No cofork. Two edges into a common target have the same source. -/
theorem no_cofork (eW : QuiverEmbedding V WillemsPosition) {x y z : V}
    (e : x ⟶ z) (f : y ⟶ z) : x = y :=
  eW.obj_inj (willems_in_degree_le_one (eW.toPre.map e) (eW.toPre.map f))

/-- No two-chain. -/
theorem no_two_chain (eW : QuiverEmbedding V WillemsPosition) {x y z : V}
    (e : x ⟶ y) (f : y ⟶ z) : False :=
  willems_no_composable (eW.toPre.map e) (eW.toPre.map f)

/-- No self-loop. -/
theorem no_loop (eW : QuiverEmbedding V WillemsPosition) {x : V} (e : x ⟶ x) :
    False :=
  no_two_chain eW e e

/-- No parallel edges. -/
theorem no_parallel (eW : QuiverEmbedding V WillemsPosition) {x y : V}
    (e f : x ⟶ y) : e = f :=
  eW.map_inj (willems_no_parallel _ _)

-- ═══════════════════════════════════════════════════════════════════════════════
-- § The structure theorem
-- ═══════════════════════════════════════════════════════════════════════════════

/-- In a quiver embedding into both the Joslyn and Willems shapes, any two edges
either have the same endpoints or share no vertex whatsoever.

A connected quiver with at least one edge therefore has exactly one edge, on two
vertices: it is `I_Klir`. -/
theorem edges_coincide_or_disjoint
    (eJ : QuiverEmbedding V JoslynPosition) (eW : QuiverEmbedding V WillemsPosition)
    {x y u v : V} (e : x ⟶ y) (f : u ⟶ v) :
    (x = u ∧ y = v) ∨ (x ≠ u ∧ y ≠ v ∧ x ≠ v ∧ y ≠ u) := by
  by_cases hxv : x = v
  · subst hxv; exact (no_two_chain eW f e).elim
  · by_cases hyu : y = u
    · subst hyu; exact (no_two_chain eW e f).elim
    · by_cases hxu : x = u
      · subst hxu; exact Or.inl ⟨rfl, no_fork eJ e f⟩
      · by_cases hyv : y = v
        · subst hyv; exact absurd (no_cofork eW e f) hxu
        · exact Or.inr ⟨hxu, hyv, hxv, hyu⟩

-- ═══════════════════════════════════════════════════════════════════════════════
-- § Connectivity, and the theorem in full
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Weak connectivity for quivers: `x` and `y` are joined by a zigzag of edges,
traversed in either direction. This is the "connected" of the theorem statement. -/
inductive Zigzag : V → V → Prop
  | refl (x : V) : Zigzag x x
  | fwd {x y z : V} : Zigzag x y → (y ⟶ z) → Zigzag x z
  | bwd {x y z : V} : Zigzag x y → (z ⟶ y) → Zigzag x z

/-- Given an edge `x ⟶ y`, nothing outside `{x, y}` is reachable from `x`.

Each step is blocked by one of the obstructions: leaving `x` forwards is a fork,
leaving `y` forwards is a two-chain, entering `x` backwards is a two-chain, and
entering `y` backwards is a cofork. -/
theorem zigzag_confined (eJ : QuiverEmbedding V JoslynPosition)
    (eW : QuiverEmbedding V WillemsPosition) {x y : V} (e : x ⟶ y) :
    ∀ {w : V}, Zigzag x w → w = x ∨ w = y := by
  intro w hw
  induction hw with
  | refl => exact Or.inl rfl
  | fwd _ g ih =>
      rcases ih with rfl | rfl
      · exact Or.inr (no_fork eJ e g).symm
      · exact (no_two_chain eW e g).elim
  | bwd _ g ih =>
      rcases ih with rfl | rfl
      · exact (no_two_chain eW g e).elim
      · exact Or.inl (no_cofork eW e g).symm

/-- **The shared primitive is a single arrow.**

A connected quiver embedding into both the Joslyn and Willems shapes, and having at
least one edge, has exactly two vertices and exactly one edge. That quiver is
`I_Klir`, whose free category is the walking arrow **2**. -/
theorem connected_is_single_arrow
    (eJ : QuiverEmbedding V JoslynPosition) (eW : QuiverEmbedding V WillemsPosition)
    (conn : ∀ a b : V, Zigzag a b) {x y : V} (e : x ⟶ y) :
    x ≠ y ∧ (∀ w : V, w = x ∨ w = y) ∧ ∀ (u v : V) (_ : u ⟶ v), u = x ∧ v = y := by
  refine ⟨?_, fun w => zigzag_confined eJ eW e (conn x w), ?_⟩
  · rintro rfl; exact no_loop eW e
  · intro u v f
    rcases zigzag_confined eJ eW e (conn x u) with rfl | rfl
    · exact ⟨rfl, (no_fork eJ e f).symm⟩
    · exact (no_two_chain eW e f).elim

-- ═══════════════════════════════════════════════════════════════════════════════
-- § The counterexample, machine-checked
--
-- The table in the header is not asserted. `V` really does embed into all eight
-- free categories, injectively on objects and faithfully, so the free-category
-- form of the maximality claim really is false.
-- ═══════════════════════════════════════════════════════════════════════════════

/-- The fork shape: one source, two arrows, two distinct sinks. -/
inductive VPos
  | src
  | left
  | right
  deriving DecidableEq, Inhabited

inductive VArrow : VPos → VPos → Type
  | toLeft : VArrow .src .left
  | toRight : VArrow .src .right

instance : Quiver VPos where Hom := VArrow

theorem v_src_self (p : Quiver.Path VPos.src VPos.src) : p = .nil := by
  cases p with
  | nil => rfl
  | cons _ e => exact nomatch e

theorem v_left_self (p : Quiver.Path VPos.left VPos.left) : p = .nil := by
  cases p with
  | nil => rfl
  | cons p e => cases e with
    | toLeft => cases p with | cons _ e' => exact nomatch e'

theorem v_right_self (p : Quiver.Path VPos.right VPos.right) : p = .nil := by
  cases p with
  | nil => rfl
  | cons p e => cases e with
    | toRight => cases p with | cons _ e' => exact nomatch e'

theorem v_no_left_src (p : Quiver.Path VPos.left VPos.src) : False := by
  cases p with | cons _ e => exact nomatch e

theorem v_no_right_src (p : Quiver.Path VPos.right VPos.src) : False := by
  cases p with | cons _ e => exact nomatch e

theorem v_src_left (p : Quiver.Path VPos.src VPos.left) :
    p = Quiver.Hom.toPath VArrow.toLeft := by
  cases p with
  | cons p e => cases e with
    | toLeft => have h := v_src_self p; subst h; rfl

theorem v_src_right (p : Quiver.Path VPos.src VPos.right) :
    p = Quiver.Hom.toPath VArrow.toRight := by
  cases p with
  | cons p e => cases e with
    | toRight => have h := v_src_self p; subst h; rfl

theorem v_no_left_right (p : Quiver.Path VPos.left VPos.right) : False := by
  cases p with
  | cons p e => cases e with
    | toRight => exact v_no_left_src p

theorem v_no_right_left (p : Quiver.Path VPos.right VPos.left) : False := by
  cases p with
  | cons p e => cases e with
    | toLeft => exact v_no_right_src p

/-- `V` is thin, so every functor out of it is faithful. -/
theorem v_path_subsingleton : ∀ (a b : VPos) (p q : Quiver.Path a b), p = q := by
  intro a b p q
  cases a <;> cases b
  · rw [v_src_self p, v_src_self q]
  · rw [v_src_left p, v_src_left q]
  · rw [v_src_right p, v_src_right q]
  · exact (v_no_left_src p).elim
  · rw [v_left_self p, v_left_self q]
  · exact (v_no_left_right p).elim
  · exact (v_no_right_src p).elim
  · exact (v_no_right_left p).elim
  · rw [v_right_self p, v_right_self q]

instance vHomSubsingleton (X Y : Paths VPos) : Subsingleton (X ⟶ Y) :=
  ⟨v_path_subsingleton X Y⟩

/-- Seven of the eight targets have a vertex of out-degree two, so `V` enters by
edges alone. -/
def vToBungePre : Prefunctor VPos (Paths BungePosition) where
  obj | .src => .structure' | .left => .composition | .right => .environment
  map | .toLeft => Quiver.Hom.toPath BungeArrow.struct_on_comp
      | .toRight => Quiver.Hom.toPath BungeArrow.struct_on_env

def vToMobusPre : Prefunctor VPos (Paths MobusPosition) where
  obj | .src => .externalFlows | .left => .environment | .right => .boundary
  map | .toLeft => Quiver.Hom.toPath MobusArrow.external_on_env
      | .toRight => Quiver.Hom.toPath MobusArrow.external_on_boundary

def vToMyersPre : Prefunctor VPos (Paths MyersPosition) where
  obj | .src => .state | .left => .output | .right => .input
  map | .toLeft => Quiver.Hom.toPath MyersArrow.expose
      | .toRight => Quiver.Hom.toPath MyersArrow.update

def vToWymorePre : Prefunctor VPos (Paths WymorePosition) where
  obj | .src => .state | .left => .input | .right => .output
  map | .toLeft => Quiver.Hom.toPath WymoreArrow.nextState
      | .toRight => Quiver.Hom.toPath WymoreArrow.readout

def vToMesarovicPre : Prefunctor VPos (Paths MesarovicPosition) where
  obj | .src => .globalState | .left => .input | .right => .output
  map | .toLeft => Quiver.Hom.toPath MesarovicArrow.response_input
      | .toRight => Quiver.Hom.toPath MesarovicArrow.response_output

def vToSpivakPre : Prefunctor VPos (Paths SpivakPosition) where
  obj | .src => .parameter | .left => .output | .right => .input
  map | .toLeft => Quiver.Hom.toPath SpivakArrow.expose
      | .toRight => Quiver.Hom.toPath SpivakArrow.update

def vToWillemsPre : Prefunctor VPos (Paths WillemsPosition) where
  obj | .src => .behavior | .left => .signal | .right => .time
  map | .toLeft => Quiver.Hom.toPath WillemsArrow.evaluate
      | .toRight => Quiver.Hom.toPath WillemsArrow.indexed_by

/-- Joslyn is the leak. No vertex has out-degree two, so `V` cannot enter by edges.
It enters by a *path*: `controller → effector → controlled`, a composite the
tradition never asserts. -/
def vToJoslynPre : Prefunctor VPos (Paths JoslynPosition) where
  obj | .src => .controller | .left => .effector | .right => .controlled
  map | .toLeft => Quiver.Hom.toPath JoslynArrow.disturbance
      | .toRight => (Quiver.Hom.toPath JoslynArrow.disturbance).comp
                      (Quiver.Hom.toPath JoslynArrow.efferent)

theorem vToBunge_obj_injective : Function.Injective vToBungePre.obj := by
  intro a b h; cases a <;> cases b <;> simp_all [vToBungePre]

theorem vToMobus_obj_injective : Function.Injective vToMobusPre.obj := by
  intro a b h; cases a <;> cases b <;> simp_all [vToMobusPre]

theorem vToMyers_obj_injective : Function.Injective vToMyersPre.obj := by
  intro a b h; cases a <;> cases b <;> simp_all [vToMyersPre]

theorem vToWymore_obj_injective : Function.Injective vToWymorePre.obj := by
  intro a b h; cases a <;> cases b <;> simp_all [vToWymorePre]

theorem vToMesarovic_obj_injective : Function.Injective vToMesarovicPre.obj := by
  intro a b h; cases a <;> cases b <;> simp_all [vToMesarovicPre]

theorem vToSpivak_obj_injective : Function.Injective vToSpivakPre.obj := by
  intro a b h; cases a <;> cases b <;> simp_all [vToSpivakPre]

theorem vToWillems_obj_injective : Function.Injective vToWillemsPre.obj := by
  intro a b h; cases a <;> cases b <;> simp_all [vToWillemsPre]

theorem vToJoslyn_obj_injective : Function.Injective vToJoslynPre.obj := by
  intro a b h; cases a <;> cases b <;> simp_all [vToJoslynPre]

theorem vToJoslyn_faithful : (Paths.lift vToJoslynPre).Faithful :=
  faithful_of_subsingleton_hom _

/-- **The free-category maximality claim is false.** `V` has three objects where
`I_Klir` has two, is connected, and embeds into all eight shape categories
injectively on objects and faithfully. -/
theorem free_category_maximality_fails :
    Function.Injective vToBungePre.obj ∧ (Paths.lift vToBungePre).Faithful ∧
    Function.Injective vToMobusPre.obj ∧ (Paths.lift vToMobusPre).Faithful ∧
    Function.Injective vToMyersPre.obj ∧ (Paths.lift vToMyersPre).Faithful ∧
    Function.Injective vToWymorePre.obj ∧ (Paths.lift vToWymorePre).Faithful ∧
    Function.Injective vToMesarovicPre.obj ∧ (Paths.lift vToMesarovicPre).Faithful ∧
    Function.Injective vToSpivakPre.obj ∧ (Paths.lift vToSpivakPre).Faithful ∧
    Function.Injective vToWillemsPre.obj ∧ (Paths.lift vToWillemsPre).Faithful ∧
    Function.Injective vToJoslynPre.obj ∧ (Paths.lift vToJoslynPre).Faithful :=
  ⟨vToBunge_obj_injective, faithful_of_subsingleton_hom _,
   vToMobus_obj_injective, faithful_of_subsingleton_hom _,
   vToMyers_obj_injective, faithful_of_subsingleton_hom _,
   vToWymore_obj_injective, faithful_of_subsingleton_hom _,
   vToMesarovic_obj_injective, faithful_of_subsingleton_hom _,
   vToSpivak_obj_injective, faithful_of_subsingleton_hom _,
   vToWillems_obj_injective, faithful_of_subsingleton_hom _,
   vToJoslyn_obj_injective, faithful_of_subsingleton_hom _⟩

/-- And `V` is strictly larger: three objects, not two. -/
theorem v_has_three_objects : ∀ (f : VPos → KlirPosition), ¬ Function.Injective f := by
  intro f hinj
  have h : f .src = f .left ∨ f .src = f .right ∨ f .left = f .right := by
    cases (f .src) <;> cases (f .left) <;> cases (f .right) <;> simp
  rcases h with h | h | h
  · exact absurd (hinj h) (by decide)
  · exact absurd (hinj h) (by decide)
  · exact absurd (hinj h) (by decide)

/-- But `V` does **not** embed at the quiver level: Joslyn has no vertex of
out-degree two. This is the whole content of the level shift. -/
theorem v_no_quiver_embedding_into_joslyn :
    IsEmpty (QuiverEmbedding VPos JoslynPosition) := by
  constructor
  intro emb
  exact absurd (no_fork emb VArrow.toLeft VArrow.toRight) (by decide)

end SharedPrimitive
