/-
  Systems/Mesarovic/Decomposition.lean
  Mesarovic 1964: the decomposition theorem's two cores

  Source: Mesarovic, "Foundations for a General Systems Theory", in
  Views on General Systems Theory (Wiley, 1964), pp. 13-17 — the
  "Decomposition and State of the System" section. Page scans acquired
  2026-07-11; full transcription + first-read analysis in
  docs/reference/mesarovic-1964-decomposition.md.

  THE THEOREM (p. 14): an nth-order relation can be (1) decomposed into
  (n - 2) triadic relations, unconditionally; (2) decomposed into dyadic
  relations IFF every triadic factor's medium term is assembled from
  terms already present (eq. 18 with Z_j = X_{i+1} ∪ X_{i+2}).

  FORMALIZED HERE — the two cores:
  - Part 1's constructive engine: `Set.peel` — any relation on A × B × C
    factors through the prefix-state Z := A × B into a triadic factor
    (the pairing graph) and a remainder. C stands for the whole tail, so
    iterating peel IS the (n - 2)-triadic decomposition; one full crank
    shown at n = 4 (`Set.quaternary_two_triadic`, 2 = 4 - 2 factors).
  - Part 2's floor, concretely: `binaryJoin_parityRel_ne` — a ternary
    relation is NOT determined by its binary shadows (parity: every
    binary projection is full, yet the join strictly exceeds it).

  NOT FORMALIZED (the research-level remainder): part 2's iff — the
  medium-term condition (18)+(b) needs its modern typing reconstructed,
  and the printed necessity proof is schematic (it exhibits the canonical
  splitting's failure; the "any splitting" generality gap must be closed).

  STATE AS COROLLARY: Mesarovic introduces the state concept as a
  consequence of this theorem (pp. 15-17): the peel's connecting term
  "represents the state of the system ... embodies the entire past
  history", and "the three terms of the triadic relation are, then,
  input, output, and state." `Set.peel`'s Z := A × B is literally that
  prefix history. This is the 1964 impossibility-face of M&T 1975
  Thm 1.1 (state always suffices); together they are the two-sided
  justification of state-based systems theory.

  RESONANCE: the dyadic floor is recognizably Peirce's reduction thesis
  (ternary irreducible to binary; ternary sufficient) in systems
  clothing. Joslyn (1995, §3.4) leans on this theorem for Prop 29
  ("O must have internal states"); Part 1 here is the leg Prop 29's
  existence direction rests on (see Systems/Joslyn/Control.lean, where
  that direction is deferred).
-/

import Mathlib.Data.Set.Basic

namespace Systems

/-! ## Part 1's engine: the peel lemma -/

/-- The triadic factor the peel produces: the graph of pairing — the
    connecting term IS the pair of the two coordinates consumed.
    Mesarovic p. 16: the connecting term "embodies the entire past
    history of the system". -/
def pairingGraph (A B : Type*) : Set (A × B × (A × B)) :=
  {p | p.2.2 = (p.1, p.2.1)}

/-- THE PEEL LEMMA (Mesarovic eq. 19, one step, modern form): any relation
    on A × B × C is the relative product of the triadic pairing graph and
    a remainder relation through the fresh state Z := A × B. Since C may
    itself be a product (the whole tail), iterating this step is exactly
    part 1 of the p. 14 theorem: (n - 2) triadic factors, unconditionally.
    Fully constructive — the witness is the prefix pair itself. -/
theorem Set.peel {A B C : Type*} (S : Set (A × B × C)) :
    ∀ p : A × B × C, p ∈ S ↔
      ∃ z : A × B, (p.1, p.2.1, z) ∈ pairingGraph A B ∧
        (z, p.2.2) ∈ {q : (A × B) × C | (q.1.1, q.1.2, q.2) ∈ S} := by
  intro p
  constructor
  · intro hp
    exact ⟨(p.1, p.2.1), rfl, hp⟩
  · rintro ⟨z, hz, hS⟩
    rw [pairingGraph] at hz
    simp only [Set.mem_setOf_eq] at hz hS
    rw [hz] at hS
    exact hS

/-- One full crank at n = 4: a quaternary relation decomposes into
    2 = (4 - 2) triadic relations through the prefix state A × B.
    The general count is this construction iterated. -/
theorem Set.quaternary_two_triadic {A B C D : Type*} (S : Set (A × B × C × D)) :
    ∃ (T₁ : Set (A × B × (A × B))) (T₂ : Set ((A × B) × C × D)),
      ∀ p : A × B × C × D, p ∈ S ↔
        ∃ z : A × B, (p.1, p.2.1, z) ∈ T₁ ∧ (z, p.2.2.1, p.2.2.2) ∈ T₂ := by
  refine ⟨pairingGraph A B, {q | (q.1.1, q.1.2, q.2.1, q.2.2) ∈ S}, fun p => ?_⟩
  constructor
  · intro hp
    exact ⟨(p.1, p.2.1), rfl, hp⟩
  · rintro ⟨z, hz, hS⟩
    rw [pairingGraph] at hz
    simp only [Set.mem_setOf_eq] at hz hS
    rw [hz] at hS
    exact hS

/-! ## Part 2's floor: the parity witness

  Every binary projection of the parity relation is full, so the join of
  its binary shadows is the whole cube — strictly larger than parity.
  A genuinely triadic relation is invisible to dyadic structure: this is
  the concrete face of "a higher order system cannot be decomposed into
  the subsystems with less than triadic relations" (p. 15, Mesarovic's
  emphasis), and the formal seed of internal state being FORCED. -/

/-- Parity: the third coordinate is determined by (and genuinely depends
    on) BOTH of the first two. -/
def parityRel : Set (Bool × Bool × Bool) :=
  {p | p.2.2 = xor p.1 p.2.1}

/-- The join of a ternary relation's three binary shadows: everything the
    dyadic projections jointly admit. Reconstruction from dyadic data can
    do no better than this. -/
def binaryJoin (S : Set (Bool × Bool × Bool)) : Set (Bool × Bool × Bool) :=
  {p | (∃ c, (p.1, p.2.1, c) ∈ S) ∧ (∃ a, (a, p.2.1, p.2.2) ∈ S) ∧
       (∃ b, (p.1, b, p.2.2) ∈ S)}

/-- Any relation sits inside the join of its own shadows. -/
theorem parityRel_subset_binaryJoin : parityRel ⊆ binaryJoin parityRel :=
  fun p hp => ⟨⟨p.2.2, hp⟩, ⟨p.1, hp⟩, ⟨p.2.1, hp⟩⟩

/-- THE DYADIC FLOOR: the join of parity's binary shadows strictly exceeds
    parity — witness (true, true, true), admitted by every shadow but
    violating parity (xor true true = false). Binary data cannot pin down
    a triadic relation; the third dimension is invisible to dyadic
    shadows. -/
theorem binaryJoin_parityRel_ne : binaryJoin parityRel ≠ parityRel := by
  intro h
  have hmem : ((true, true, true) : Bool × Bool × Bool) ∈ binaryJoin parityRel := by
    refine ⟨⟨false, rfl⟩, ⟨false, rfl⟩, ⟨false, rfl⟩⟩
  rw [h] at hmem
  exact Bool.noConfusion hmem

end Systems
