import TypeSystemsInLean.Common.Relation

/-!
# Closures of Relations

This module provides definitions for various closures of binary relations:
- Reflexive closure
- Transitive closure
- Reflexive-transitive closure

## Main definitions

- `IsReflexiveClosure`: Reflexive closure predicate
- `IsTransitiveClosure`: Transitive closure predicate
- `IsReflTransClosure`: Reflexive-transitive closure predicate
- `reflClosure`: Explicit construction of reflexive closure
- `RTC`: Inductive reflexive-transitive closure
-/

namespace TypeSystems

universe u

open Relation

variable {α : Type u}

/-- Reflexive property -/
def Reflexive (R : Rel' α) : Prop :=
  ∀ s : α, R s s

/-- Transitive property -/
def Transitive (R : Rel' α) : Prop :=
  ∀ ⦃s t u : α⦄, R s t → R t u → R s u

/-- R' is the reflexive closure of R -/
def IsReflexiveClosure (R R' : Rel' α) : Prop :=
  SubRel R R' ∧
  Reflexive R' ∧
  ∀ R'' : Rel' α,
    SubRel R R'' →
    Reflexive R'' →
    SubRel R' R''

/-- R' is the transitive closure of R -/
def IsTransitiveClosure (R R' : Rel' α) : Prop :=
  SubRel R R' ∧
  Transitive R' ∧
  ∀ R'' : Rel' α,
    SubRel R R'' →
    Transitive R'' →
    SubRel R' R''

/-- R' is the reflexive-transitive closure of R -/
def IsReflTransClosure (R R' : Rel' α) : Prop :=
  SubRel R R' ∧
  Reflexive R' ∧
  Transitive R' ∧
  ∀ R'' : Rel' α,
    SubRel R R'' →
    Reflexive R'' →
    Transitive R'' →
    SubRel R' R''

/-- Explicit construction of reflexive closure -/
def reflClosure (R : Rel' α) : Rel' α :=
  fun s t => R s t ∨ s = t

/-- One step of transitive closure construction -/
def stepTrans (R' : Rel' α) : Rel' α :=
  fun s u =>
    R' s u ∨ ∃ t : α, R' s t ∧ R' t u

/-- Iterated transitive closure construction -/
def Ri (R : Rel' α) : Nat → Rel' α
| 0 => R
| n + 1 => stepTrans (Ri R n)

/-- Transitive closure as union of all iterations -/
def transClosure (R : Rel' α) : Rel' α :=
  fun s t => ∃ i : Nat, Ri R i s t

/-- Inductive definition of reflexive-transitive closure (R*) -/
inductive RTC (R : Rel' α) : Rel' α
| refl : ∀ s : α, RTC R s s
| tail : ∀ {s t u : α}, R s t → RTC R t u → RTC R s u

-- Theorems

/-- reflClosure is indeed the reflexive closure -/
theorem reflClosure_isReflexiveClosure (R : Rel' α) :
    IsReflexiveClosure R (reflClosure R) :=
    ⟨
      -- R ⊆ R'
      (fun {_ _} h => Or.inl h),
      -- R' is reflexive
      (fun s => Or.inr rfl),
      -- R' is minimal
      (fun R'' hRR'' hRefl {_ _} h =>
        Or.elim h
          (fun hR => hRR'' hR)
          (fun hEq => Eq.ndrec (hRefl _) hEq))
    ⟩

/-- If P is preserved by R, then P is preserved by R* -/
theorem preservedBy_RTC
    (P : α → Prop)
    (R : Rel' α)
    (hPR : PreservedBy P R) :
    PreservedBy P (RTC R) := by
    intro s t hst hPs
    induction hst with
    | refl s =>
      exact hPs
    | tail hR _ ih =>
      exact ih (hPR hR hPs)

end TypeSystems
