import Mathlib.Data.Set.Basic

/-!
# Relations

This module provides abstract definitions for binary relations.
These definitions are reusable across different chapters.

## Main definitions

- `Rel`: Binary relation type
- `SubRel`: Relation inclusion
- `dom`: Domain of a relation
- `ran`: Range of a relation
- `IsPartialFunction`: Partial function predicate
- `IsTotalFunction`: Total function predicate
- `PreservedBy`: Property preservation by a relation
-/

namespace TypeSystems

universe u v

/-- Binary relation on types `α` and `β` -/
abbrev Rel (α : Type u) (β : Type v) := α → β → Prop

/-- Binary relation on a single type `α` -/
abbrev Rel' (α : Type u) := α → α → Prop

variable {α : Type u} {β : Type v}

/-- Relation inclusion: `R ⊆ R'` -/
def SubRel (R R' : Rel α β) : Prop :=
  ∀ ⦃s t⦄, R s t → R' s t

infix:50 " ⊆ᵣ " => SubRel

/-- Domain of a relation (as a set) -/
def dom (R : Set (α × β)) : Set α :=
  {x | ∃ y, (x, y) ∈ R}

/-- Range of a relation (as a set) -/
def ran (R : Set (α × β)) : Set β :=
  {y | ∃ x, (x, y) ∈ R}

/-- Domain of a relation (as a predicate) -/
def domRel (R : Rel α β) : Set α :=
  {x | ∃ y, R x y}

/-- Range of a relation (as a predicate) -/
def ranRel (R : Rel α β) : Set β :=
  {y | ∃ x, R x y}

/-- A relation is a partial function if each input has at most one output -/
def IsPartialFunction (S : Set α) (T : Set β) (R : Set (α × β)) : Prop :=
  R ⊆ (S ×ˢ T) ∧
  ∀ x y₁ y₂,
    (x, y₁) ∈ R →
    (x, y₂) ∈ R →
    y₁ = y₂

/-- A relation is a total function if it's a partial function defined on all of S -/
def IsTotalFunction (S : Set α) (T : Set β) (R : Set (α × β)) : Prop :=
  IsPartialFunction S T R ∧ dom R = S

/-- Alternative definition: total function using unique existence -/
def IsTotalFunction' (S : Set α) (T : Set β) (R : Set (α × β)) : Prop :=
  R ⊆ (S ×ˢ T) ∧
  ∀ x, x ∈ S → ∃! y, (x, y) ∈ R

/-- A relation is functional if each input has at most one output -/
def IsFunctional (R : Set (α × β)) : Prop :=
  ∀ x y₁ y₂,
    (x, y₁) ∈ R →
    (x, y₂) ∈ R →
    y₁ = y₂

/-- A relation is surjective onto T if every element of T is in the range -/
def IsSurjective (R : Set (α × β)) (T : Set β) : Prop :=
  ∀ y ∈ T, ∃ x, (x, y) ∈ R

/-- Value is defined at a point -/
def DefinedAt (R : Set (α × β)) (x : α) : Prop :=
  x ∈ dom R

/-- Value is undefined at a point -/
def UndefinedAt (R : Set (α × β)) (x : α) : Prop :=
  x ∉ dom R

/-- A property P is preserved by relation R -/
def PreservedBy (P : α → Prop) (R : Rel' α) : Prop :=
  ∀ ⦃s t⦄, R s t → P s → P t

/-- A property P is preserved by a relation (set version) -/
def PreservedBySet (P : α → Prop) (R : Set (α × α)) : Prop :=
  ∀ s t, (s, t) ∈ R → P s → P t

-- Basic theorems

theorem definedAt_iff_exists (R : Set (α × β)) (x : α) :
    DefinedAt R x ↔ ∃ y, (x, y) ∈ R := by
  rfl

theorem undefinedAt_iff_not_exists (R : Set (α × β)) (x : α) :
    UndefinedAt R x ↔ ¬ ∃ y, (x, y) ∈ R := by
  rfl

end TypeSystems
