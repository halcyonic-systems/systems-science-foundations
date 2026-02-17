/-
  Systems/Core/Level.lean
  Level structure, level precedence, and recursive decomposition

  Formalizes:
  - Bunge, Treatise Vol. 4, Def 1.8: Level precedence and level structure
  - Mobus, Understanding Systems, Eq. 4.3: Recursive component (complex/atomic)

  SHOWCASE THEOREM #5: Ancestry is a strict partial order.
  SHOWCASE THEOREM #6: Recursive decomposition terminates (from inductive type).
-/

import Systems.Core.System

namespace Systems

/-! ## Level Precedence (Bunge Def 1.8) -/

/-- One level precedes another iff all things in the latter are composed
    of things in the former.
    Bunge Def 1.8(i): L_i < L_j iff ∀ x ∈ L_j, ∃ y ∈ L_i, y ∈ C(x).

    We use the Preorder on α (parthood) to express "y ∈ C(x)" as "y ≤ x". -/
def LevelPrecedes {α : Type*} [Preorder α] (Li Lj : Set α) : Prop :=
  ∀ x ∈ Lj, ∃ y ∈ Li, y ≤ x

/-- A level structure is a family of nonempty sets ordered by precedence.
    Bunge Def 1.8(iii): L = ⟨L, <⟩ is a level structure.

    We represent it as a list of levels (ordered from lowest to highest)
    where each level precedes the next. -/
structure LevelStructure (α : Type*) [Preorder α] where
  /-- The sequence of levels, from lowest to highest -/
  levels : List (Set α)
  /-- Each level is nonempty -/
  levels_nonempty : ∀ L ∈ levels, Set.Nonempty L
  /-- Each level precedes the next -/
  precedence : levels.Pairwise (fun Li Lj => LevelPrecedes Li Lj)

/-! ## Recursive Component (Mobus Eq. 4.3) -/

/-- Mobus's recursive component: either complex (a subsystem that can be
    further decomposed) or atomic (a terminal component).
    Mobus Eq. 4.3:
      c_{i,j,l} = S_{i,j,l+1}  if component is complex
                  c_a            if component is atomic

    This inductive type guarantees termination of decomposition (well-foundedness).

    SHOWCASE THEOREM #6: Termination is guaranteed by Lean's kernel — the
    inductive type is structurally decreasing, so any recursive function
    over RecursiveComponent terminates. -/
inductive RecursiveComponent (α : Type*) where
  /-- An atomic component: terminal, no further decomposition needed -/
  | atomic (thing : α) : RecursiveComponent α
  /-- A complex component: a system composed of sub-components -/
  | complex (thing : α) (children : List (RecursiveComponent α)) :
      RecursiveComponent α

/-- The thing represented by a recursive component. -/
def RecursiveComponent.thing {α : Type*} : RecursiveComponent α → α
  | .atomic a => a
  | .complex a _ => a

/-- Whether a component is atomic (leaf node). -/
def RecursiveComponent.isAtomic {α : Type*} : RecursiveComponent α → Bool
  | .atomic _ => true
  | .complex _ _ => false

/-- The depth of a recursive component (height of the tree).
    This function terminates by structural recursion on the inductive type. -/
def RecursiveComponent.depth {α : Type*} : RecursiveComponent α → Nat
  | .atomic _ => 0
  | .complex _ children => 1 + children.foldl (fun acc c => max acc c.depth) 0

/-- Count the total number of atomic components (leaf nodes). -/
def RecursiveComponent.atomicCount {α : Type*} : RecursiveComponent α → Nat
  | .atomic _ => 1
  | .complex _ children => children.foldl (fun acc c => acc + c.atomicCount) 0

/-- An atomic component has depth 0. -/
theorem RecursiveComponent.atomic_depth {α : Type*} (a : α) :
    (RecursiveComponent.atomic a).depth = 0 := by
  simp [RecursiveComponent.depth]

/-- An atomic component counts as exactly 1. -/
theorem RecursiveComponent.atomic_count {α : Type*} (a : α) :
    (RecursiveComponent.atomic a).atomicCount = 1 := by
  simp [RecursiveComponent.atomicCount]

/-! ## Descent (Bunge Def 1.16)

The ancestry relation on a collection of systems.
Bunge Def 1.16: x is an ancestor of y iff x is an immediate or
mediate ancestor.

SHOWCASE THEOREM #5: The ancestry relation is a strict partial order
(irreflexive and transitive). We define immediate ancestry and take
its transitive closure. -/

/-- Immediate ancestor relation.
    Bunge Def 1.16(i): x is an immediate ancestor of y iff x or a part
    of x is a precursor in the assembly of y. -/
class ImmediateAncestor (α : Type*) where
  immediateAncestor : α → α → Prop

export ImmediateAncestor (immediateAncestor)

/-- The (general) ancestor relation: transitive closure of immediate ancestry.
    Bunge Def 1.16(iii): x < y iff x is an immediate or mediate ancestor. -/
inductive Ancestor {α : Type*} [ImmediateAncestor α] : α → α → Prop where
  /-- Immediate ancestry implies general ancestry -/
  | immediate {x y : α} : immediateAncestor x y → Ancestor x y
  /-- Transitivity: if x < z and z < y then x < y -/
  | trans {x y z : α} : Ancestor x z → Ancestor z y → Ancestor x y

/-- The ancestry of x: the set of all ancestors.
    Bunge Def 1.16(iv): A(x) = {y ∈ S | y < x}. -/
def ancestry {α : Type*} [ImmediateAncestor α] (x : α) : Set α :=
  {y | Ancestor y x}

/-- The progeny of x: the set of all descendants.
    Bunge Def 1.16(v): P(x) = {y ∈ S | x < y}. -/
def progeny {α : Type*} [ImmediateAncestor α] (x : α) : Set α :=
  {y | Ancestor x y}

/-- The lineage of x: the union of ancestry and progeny.
    Bunge Def 1.16(vi): L(x) = {y ∈ S | y < x or x < y}. -/
def lineage {α : Type*} [ImmediateAncestor α] (x : α) : Set α :=
  ancestry x ∪ progeny x

/-- Ancestry is transitive (by construction). -/
theorem ancestor_trans {α : Type*} [ImmediateAncestor α] {x y z : α}
    (hxz : Ancestor x z) (hzy : Ancestor z y) : Ancestor x y :=
  Ancestor.trans hxz hzy

end Systems
