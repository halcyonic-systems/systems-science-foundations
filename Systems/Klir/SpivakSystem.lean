/-
  Systems/Klir/SpivakSystem.lean
  The data-level Spivak view: energy-driven systems and the cost of the eighth entry

  ShapeSpivak.lean carries entry #8 at the shape+embedding standard. This
  file carries it at the data level, joining Klir, Bunge, and Mobus in
  ViewGeneration.lean's regime: a concrete structure, a generated view,
  round trips, and a named cost.

  THE HONEST DATUM: SpivakSystem is shaped after CLS24 Definition 7
  (Capucci-Lynch-Spivak, arXiv:2404.16140): an open energy-driven system
  is (state, reaction, energy, exposure). This is the tradition's own
  concrete single-system statement; the categorical datum of Spivak 2026
  Def 4.1.1 (arXiv:2606.28984) is how such systems COMPOSE, deferred here
  exactly as MobusSystem defers Mobus's network machinery.

  THE FACTORIZATION LAW: a bare tuple with independent potential and step
  fields would admit a degenerate instance whose potential does nothing —
  formalizing a strawman. The commitment "value drives motion" is
  therefore structure, not decoration: `step_drives` forces every step to
  factor through the potential via the reaction, and `reaction_const` is
  the Set-level shadow of the reaction being a bundle map T*X → TX that
  sends the zero covector to zero motion. Constant potential provably
  yields no dynamics (`potentialFree_static`) — the degenerate case is
  not an error but a stratum Spivak himself names (Def 5.3.2:
  potential-free, static, stateless).

  WHAT THE SPIVAK VIEW COSTS (the finding): unlike Bunge's bond and
  Mobus's irreflexivity — conditions on (T, R) a kernel may already
  satisfy — a value channel is DATA the kernel cannot supply. The
  generated view is unconditional, and the cost appears as a stratum:
  every kernel-generated Spivak view is potential-free and static
  (`toSpivak_potentialFree`, `toSpivak_static`). The kernel is pure
  exposed structure — all how-it-is, no why-it-moves. Escaping the
  stratum requires a potential supplied from outside (`toSpivakWith`).

  CASTING: mirroring the shape-level embedding (klirToSpivak), things
  land in `output` and the dependency lands in `parameter` — the kernel's
  relation cast in the state role. Note the generated view is input-
  trivial but OPEN in Spivak's sense (Def 5.3.2 closed = I → I): it
  exposes the kernel's things, which is precisely what the round trip
  recovers.

  Independence caveat (carried from ShapeSpivak.lean): Spivak shares
  community and lens machinery with Myers; the commitment is new, the
  sociological independence is weaker than for the original seven.
-/

import Systems.Klir.ViewGeneration

namespace Systems

/-! ## The Spivak system -/

/-- An open energy-driven system at the data level (CLS24 Def 7): exposed
    relata, a reactive state, a potential valuing states per input, and a
    reaction converting valuations into motion. The step is not a free
    field — `step_drives` forces it to factor through the potential, and
    `reaction_const` pins the reaction's zero-covector behavior. Together
    they make "value drives motion" structural: motion cannot bypass
    value. -/
structure SpivakSystem (α In V : Type*) where
  /-- N⁺: the exposed relata. -/
  output : Set α
  /-- Q: the reactive state — the dependency cast in the state role. -/
  parameter : Set (α × α)
  /-- State pairs lie among the exposed relata. -/
  exposes : ∀ p ∈ parameter, p.1 ∈ output ∧ p.2 ∈ output
  /-- U: inputs parameterize a valuation of states. -/
  potential : In → (α × α) → V
  /-- ♯: the reaction, converting a valuation into motion. The
      nomological slot — conservative vs dissipative physics is a choice
      of reaction with the potential held fixed. -/
  reaction : ((α × α) → V) → (α × α) → (α × α)
  /-- The zero-covector law: a constant valuation has no gradient, so the
      reaction induces no motion. Set-level shadow of the reaction being
      a bundle map over the state space. -/
  reaction_const : ∀ (c : V) (p : α × α), reaction (fun _ => c) p = p
  /-- The dynamics induced by each input. -/
  step : In → (α × α) → (α × α)
  /-- The factorization law: every step routes through the potential. -/
  step_drives : ∀ i, step i = reaction (potential i)

/-! ## The Def 5.3.2 classifier

  Spivak names the degenerate strata of his own vocabulary
  (Def 5.3.2): potential-free, static, stateless, closed. The classifier
  Props below let the generated view's degeneracy be a theorem in the
  tradition's own terms rather than an error case. -/

/-- Potential-free (Def 5.3.2): every input's valuation is constant in
    the state — value distinguishes nothing. -/
def SpivakSystem.PotentialFree {α In V : Type*} (S : SpivakSystem α In V) : Prop :=
  ∀ (i : In) (p q : α × α), S.potential i p = S.potential i q

/-- Static (Def 5.3.2): no input moves the state. -/
def SpivakSystem.Static {α In V : Type*} (S : SpivakSystem α In V) : Prop :=
  ∀ i, S.step i = id

/-- Stateless (Def 5.3.2): the state space is trivial (Q ≅ 1). -/
def SpivakSystem.Stateless {α In V : Type*} (S : SpivakSystem α In V) : Prop :=
  ∀ p ∈ S.parameter, ∀ q ∈ S.parameter, p = q

/-- Driven: some input actually moves the state — the system escapes the
    static stratum. -/
def SpivakSystem.Driven {α In V : Type*} (S : SpivakSystem α In V) : Prop :=
  ¬S.Static

/-- THE CLASSIFIER BITE: a potential-free system is static. The
    factorization law leaves motion nowhere to come from once value
    distinguishes nothing. This is what a bare tuple could not prove —
    with independent fields, a do-nothing potential coexists with
    arbitrary dynamics. -/
theorem SpivakSystem.potentialFree_static {α In V : Type*}
    (S : SpivakSystem α In V) (h : S.PotentialFree) : S.Static := by
  intro i
  funext p
  have hconst : S.potential i = fun _ => S.potential i p :=
    funext fun q => h i q p
  rw [S.step_drives i, hconst]
  exact S.reaction_const _ p

/-- The cost, gate-flavored: dynamics costs value. A driven system cannot
    be potential-free. -/
theorem SpivakSystem.driven_not_potentialFree {α In V : Type*}
    (S : SpivakSystem α In V) (hd : S.Driven) : ¬S.PotentialFree :=
  fun hp => hd (S.potentialFree_static hp)

/-! ## Value is data the kernel cannot supply — the differ-in-kind theorem

  Bunge's bond and Mobus's irreflexivity are *conditions* on (T, R); the
  kernel may already satisfy them. Spivak's cost is not a condition but a
  *value type*. The theorems below make the distinction precise and general:
  over a trivial value type — everything the kernel alone carries (`toSpivak`
  uses `V = PUnit`) — a Spivak system provably cannot be driven. Drivenness
  requires a non-trivial value type supplied from outside (`toSpivakWith`).
  This is the exact sense in which the value maximum differs in kind from the
  structural elaborations: it charges no precondition, but it can only ever
  land in the static stratum unless external value data is added. -/

/-- A trivial value type cannot distinguish states: every Spivak system whose
    value type is a subsingleton is potential-free. -/
theorem SpivakSystem.subsingleton_value_potentialFree {α In V : Type*}
    [Subsingleton V] (S : SpivakSystem α In V) : S.PotentialFree :=
  fun _ _ _ => Subsingleton.elim _ _

/-- Hence static: value that distinguishes nothing leaves motion nowhere to
    come from (via the factorization law). -/
theorem SpivakSystem.subsingleton_value_static {α In V : Type*}
    [Subsingleton V] (S : SpivakSystem α In V) : S.Static :=
  S.potentialFree_static S.subsingleton_value_potentialFree

/-- **Drivenness requires a non-trivial value type, which the kernel does not
    carry.** Over a subsingleton value type — all the kernel alone supplies —
    no Spivak system is driven. `Kernel.toSpivak` (`V = PUnit`) is the instance:
    the kernel always enters Spivak's world, but only its static stratum;
    escaping it needs value data from outside (`toSpivakWith`). This is the
    value elaboration's cost stated as a theorem, in kind distinct from the
    (T, R)-conditions charged by Bunge and Mobus. -/
theorem SpivakSystem.subsingleton_value_not_driven {α In V : Type*}
    [Subsingleton V] (S : SpivakSystem α In V) : ¬S.Driven :=
  fun hd => hd S.subsingleton_value_static

/-! ## The generated view

  Following the pattern of toBunge and toMobus, the elaboration slots are
  filled with the minimal canonical witness: trivial input, trivial value,
  the inert reaction. Unlike Bunge and Mobus, no precondition is charged —
  the cost surfaces as the stratum the generated view provably occupies. -/

/-- Generate the Spivak view: the kernel as an energy-driven system with
    the minimal value channel. Unconditional — the kernel always enters
    Spivak's world, but only into its degenerate stratum. -/
def Kernel.toSpivak {α : Type*} (k : Kernel α) : SpivakSystem α PUnit PUnit where
  output := k.things
  parameter := k.dep
  exposes := k.dep_on
  potential := fun _ _ => PUnit.unit
  reaction := fun _ p => p
  reaction_const := fun _ _ => rfl
  step := fun _ p => p
  step_drives := fun _ => rfl

/-- COST (stratum form, part one): the generated view is potential-free.
    A value channel is data (T, R) cannot supply — contrast the Bunge and
    Mobus costs, which are conditions the kernel may already satisfy. -/
theorem Kernel.toSpivak_potentialFree {α : Type*} (k : Kernel α) :
    k.toSpivak.PotentialFree :=
  fun _ _ _ => rfl

/-- COST (stratum form, part two): the generated view is static. The
    kernel is pure exposed structure — all how-it-is, no why-it-moves. -/
theorem Kernel.toSpivak_static {α : Type*} (k : Kernel α) :
    k.toSpivak.Static :=
  fun _ => rfl

/-! ## Round trip and faithfulness -/

/-- Project a Spivak system to its Klir content: exposed relata and state
    pairs — the (T, R) it elaborates. -/
def SpivakSystem.toKlir {α In V : Type*} (S : SpivakSystem α In V) : KlirSystem α where
  things := S.output
  relation := S.parameter

/-- Round trip (Spivak): the generated view projects back to the kernel's
    (T, R) — the value elaboration adds a channel but loses nothing. -/
theorem Kernel.toSpivak_toKlir {α : Type*} (k : Kernel α) :
    k.toSpivak.toKlir = k.toKlir := rfl

/-- Faithfulness (Spivak): distinct kernels generate distinct views. -/
theorem Kernel.toSpivak_injective {α : Type*} :
    Function.Injective (Kernel.toSpivak (α := α)) := by
  intro k₁ k₂ h
  apply Kernel.toKlir_injective
  rw [← Kernel.toSpivak_toKlir k₁, ← Kernel.toSpivak_toKlir k₂, h]

/-! ## Escaping the stratum

  The converse that makes the cost theorem bite: supplied value data —
  a potential and a reaction from outside the kernel — can drive the
  view out of the static stratum, while still fixing the same kernel. -/

/-- Generate a Spivak view with a supplied value channel. The step is
    derived, never free: the factorization law holds by construction. -/
def Kernel.toSpivakWith {α : Type*} (k : Kernel α) {In V : Type*}
    (U : In → (α × α) → V)
    (r : ((α × α) → V) → (α × α) → (α × α))
    (hr : ∀ (c : V) (p : α × α), r (fun _ => c) p = p) :
    SpivakSystem α In V where
  output := k.things
  parameter := k.dep
  exposes := k.dep_on
  potential := U
  reaction := r
  reaction_const := hr
  step := fun i => r (U i)
  step_drives := fun _ => rfl

/-- The enriched view still fixes the kernel: same round trip. -/
theorem Kernel.toSpivakWith_toKlir {α : Type*} (k : Kernel α) {In V : Type*}
    (U : In → (α × α) → V) (r : ((α × α) → V) → (α × α) → (α × α))
    (hr : ∀ (c : V) (p : α × α), r (fun _ => c) p = p) :
    (k.toSpivakWith U r hr).toKlir = k.toKlir := rfl

/-- Supplied value data escapes the stratum: if the reaction moves any
    state under some input's potential, the enriched view is driven. With
    `driven_not_potentialFree`, such a view provably carries a nontrivial
    potential — value earned, not decorated. -/
theorem Kernel.toSpivakWith_driven {α : Type*} (k : Kernel α) {In V : Type*}
    (U : In → (α × α) → V) (r : ((α × α) → V) → (α × α) → (α × α))
    (hr : ∀ (c : V) (p : α × α), r (fun _ => c) p = p)
    (h : ∃ (i : In) (p : α × α), r (U i) p ≠ p) :
    (k.toSpivakWith U r hr).Driven := by
  intro hstatic
  obtain ⟨i, p, hne⟩ := h
  exact hne (congrFun (hstatic i) p)

end Systems
