import TypeSystemsInLean.Common.Closure

/-!
# Orders and Equivalence Relations

This module provides abstract definitions for various order relations
and equivalence relations.

## Main definitions

### Basic properties
- `Symmetric`: Symmetry property
- `Antisymmetric`: Antisymmetry property
- `Total`: Totality property

### Order types
- `IsPreorder`: Preorder (reflexive + transitive)
- `IsPartialOrder`: Partial order (preorder + antisymmetric)
- `IsTotalOrder`: Total order (partial order + total)
- `IsEquivalence`: Equivalence relation (reflexive + symmetric + transitive)

### Lattice operations
- `StrictPart`: Strict part of a relation (< from ≤)
- `IsJoin`: Join (least upper bound)
- `IsMeet`: Meet (greatest lower bound)

### Well-foundedness
- `IsDecreasingChain`: Decreasing chain
- `WellFounded`: Well-founded relation (no infinite descending chains)
-/

namespace TypeSystems

universe u

variable {α : Type u}

-- Basic relation properties

/-- Symmetric property -/
def Symmetric (R : Rel' α) : Prop :=
  ∀ ⦃s t⦄, R s t → R t s

/-- Antisymmetric property -/
def Antisymmetric (R : Rel' α) : Prop :=
  ∀ ⦃s t⦄, R s t → R t s → s = t

/-- Total (comparable) property -/
def Total (R : Rel' α) : Prop :=
  ∀ s t : α, R s t ∨ R t s

-- Order relations

/-- Preorder: reflexive and transitive -/
def IsPreorder (R : Rel' α) : Prop :=
  Reflexive R ∧ Transitive R

/-- Partial order: preorder + antisymmetric -/
def IsPartialOrder (R : Rel' α) : Prop :=
  IsPreorder R ∧ Antisymmetric R

/-- Total order: partial order + total -/
def IsTotalOrder (R : Rel' α) : Prop :=
  IsPartialOrder R ∧ Total R

/-- Equivalence relation: reflexive + symmetric + transitive -/
def IsEquivalence (R : Rel' α) : Prop :=
  Reflexive R ∧ Symmetric R ∧ Transitive R

-- Strict part of a relation

/-- Strict part: R s t ∧ s ≠ t (< from ≤) -/
def StrictPart (R : Rel' α) (s t : α) : Prop :=
  R s t ∧ s ≠ t

-- Lattice operations

/-- j is the join (least upper bound) of s and t -/
def IsJoin (R : Rel' α) (s t j : α) : Prop :=
  R s j ∧
  R t j ∧
  ∀ k : α, R s k → R t k → R j k

/-- m is the meet (greatest lower bound) of s and t -/
def IsMeet (R : Rel' α) (s t m : α) : Prop :=
  R m s ∧
  R m t ∧
  ∀ n : α, R n s → R n t → R n m

-- Well-foundedness

/-- Decreasing chain: c(i+1) < c(i) for all i -/
def IsDecreasingChain (R : Rel' α) (c : Nat → α) : Prop :=
  ∀ i : Nat, StrictPart R (c (i + 1)) (c i)

/-- Well-founded: no infinite descending chains -/
def WellFounded (R : Rel' α) : Prop :=
  ¬ ∃ c : Nat → α, IsDecreasingChain R c

end TypeSystems
