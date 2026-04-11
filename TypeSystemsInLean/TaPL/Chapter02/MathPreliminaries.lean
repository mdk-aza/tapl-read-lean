import Mathlib.Data.Set.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic
import Mathlib
import TypeSystemsInLean.Common.Relation
import TypeSystemsInLean.Common.Closure
import TypeSystemsInLean.Common.Order

/-!
# Chapter 2: Mathematical Preliminaries

This chapter covers the mathematical foundations needed for the study of type systems.

## Contents

- **Section 2.1**: Sets, Relations, and Functions
- **Section 2.2**: Ordered Sets
- **Section 2.3**: Sequences
- **Section 2.4**: Induction

## Lean Tactics Quick Reference

- `rfl` - 定義そのまま (reflexivity)
- `decide` - 計算で終わる (decidable propositions)
- `intro` - 仮定を使う (introduce hypothesis)
- `rcases` - 存在を扱う (case analysis on existentials)
- `exact` - 答えを置く (provide exact proof term)
- `omega` / `linarith` - 数学的に詰める (arithmetic/linear arithmetic solver)
-/

open Set
open List
open TypeSystems

-- ========================================================================
-- Section 2.1: Sets, Relations, and Functions
-- ========================================================================

/-!
## 2.1 核心概念

Leanにおける集合と関係の表現：
- **Prop** = 真か偽かを表すもの（命題）
- **証明** = Propを作ること
- **集合** = 条件（Propを返す関数: `α → Prop`）
- **関係** = 二項の条件（`α → β → Prop`）

重要な対応：
- 集合 = 条件
- 関係 = 条件を満たす組
- dom = ∃で取り出す
- 関数 = ∃ + 一意
- 部分関数 = ∃がない場合もある
- 保存 = 関係で進んでも条件が保たれる
-/

namespace Chapter02

variable {α β : Type}

-- ------------------------------------------------------------------------
-- 2.1.1: Sets
-- ------------------------------------------------------------------------

/-- 部分集合の基本例 -/
example (S T : Set α) : Prop := S ⊆ T

/-- 差集合の定義 -/
example (S T : Set α) :
    S \ T = {x | x ∈ S ∧ x ∉ T} := by rfl

/-- べき集合の定義 -/
example (S : Set α) :
    Set.powerset S = {T | T ⊆ S} := by rfl

/-- べき集合の別の表現 -/
example (S : Set α) :
    Set.powerset S = {T | ∀ x, x ∈ T → x ∈ S} := by rfl

-- 具体例：自然数の集合

def Small : Set Nat := {x | x ≤ 5}
def Tiny : Set Nat := {x | x ≤ 2}
def Even (n : Nat) : Prop := ∃ k, n = 2 * k
def EvenSet : Set Nat := {n | Even n}
def SmallEven : Set Nat := {x | x ≤ 4 ∧ Even x}

example : 3 ∈ Small := by show 3 ≤ 5; decide
example : 7 ∉ Small := by show ¬(7 ≤ 5); decide
example : 4 ∈ EvenSet := ⟨2, by decide⟩

example : 3 ∉ EvenSet := by
  intro h
  rcases h with ⟨k, hk⟩
  omega

example : Tiny ⊆ Small := by
  intro x hx
  simp [Tiny] at hx
  simp [Small]
  exact le_trans hx (by decide)

example : SmallEven ⊆ Small := by
  intro x hx
  simp [SmallEven] at hx
  simp [Small]
  rcases hx with ⟨h1, _⟩
  exact le_trans h1 (by decide)

-- 差集合の例
example : 3 ∈ Small \ EvenSet := by
  refine ⟨?_, ?_⟩
  · simp [Small]
  · intro h
    rcases h with ⟨k, hk⟩
    omega

example : 4 ∉ Small \ EvenSet := by
  intro h
  exact h.2 (by show Even 4; exact ⟨2, by decide⟩)

-- べき集合の例
def A : Set Nat := {x | x = 0 ∨ x = 1}
def B : Set Nat := {x | x = 0}

example : B ∈ Set.powerset A := by
  show B ⊆ A
  intro x hx
  dsimp [B, A] at hx ⊢
  left
  exact hx

-- ------------------------------------------------------------------------
-- 2.1.2: Countable Sets
-- ------------------------------------------------------------------------

/-- 可算集合の定義: 自然数と一対一対応がある -/
def isCountable (S : Set α) : Prop :=
  Nonempty (Nat ≃ {x // x ∈ S})

example : isCountable (Set.univ : Set Nat) := by
  refine ⟨?_⟩
  refine
    { toFun := fun n => ⟨n, by trivial⟩
      invFun := fun x => x.val
      left_inv := by intro n; rfl
      right_inv := by intro x; cases x; rfl }

-- ------------------------------------------------------------------------
-- 2.1.3: Relations
-- ------------------------------------------------------------------------

/-- n項関係（ここでは2項関係）-/
def Rel₂ (S₁ : Set α) (S₂ : Set β) :=
  {R : Set (α × β) // R ⊆ (S₁ ×ˢ S₂)}

-- ------------------------------------------------------------------------
-- 2.1.4: Predicates (Unary Relations)
-- ------------------------------------------------------------------------

/-- 単項関係 = 述語 -/
def Predicate := α → Prop

/-- 集合の要素性と述語の適用は同じ -/
example (P : Set α) (s : α) :
    s ∈ P ↔ P s := by rfl

-- ------------------------------------------------------------------------
-- 2.1.5: Binary Relations (Infix Notation)
-- ------------------------------------------------------------------------

example (R : Set (α × β)) (s : α) (t : β) : Prop :=
  (s, t) ∈ R

example (R : α → β → Prop) (s : α) (t : β) : Prop :=
  R s t

-- ------------------------------------------------------------------------
-- 2.1.6: Ternary Relations (Typing Judgments)
-- ------------------------------------------------------------------------

section TypingExample

variable {Ctx Term Ty : Type}

/-- 型付け関係の例 -/
def Typing : Ctx → Term → Ty → Prop :=
  fun _ _ _ => True

notation:50 Γ " ⊢ " s " : " T => Typing Γ s T

example (_Γ : Ctx) (_s : Term) (_T : Ty) :
    (_Γ ⊢ _s : _T) ↔ Typing _Γ _s _T := by rfl

end TypingExample

-- ------------------------------------------------------------------------
-- 2.1.7: Domain and Range
-- ------------------------------------------------------------------------

-- Using definitions from Common.Relation

example (R : Set (α × β)) (s : α) :
    s ∈ dom R ↔ ∃ t, (s, t) ∈ R := by rfl

example (R : Set (α × β)) (t : β) :
    t ∈ ran R ↔ ∃ s, (s, t) ∈ R := by rfl

-- ------------------------------------------------------------------------
-- 2.1.8: Partial and Total Functions
-- ------------------------------------------------------------------------

-- Definitions provided by Common.Relation: IsPartialFunction, IsTotalFunction

-- ------------------------------------------------------------------------
-- 2.1.9: Definedness
-- ------------------------------------------------------------------------

-- Definitions provided by Common.Relation: DefinedAt, UndefinedAt

-- ------------------------------------------------------------------------
-- 2.1.10: Preservation
-- ------------------------------------------------------------------------

-- Definition provided by Common.Relation: PreservedBy

-- ========================================================================
-- Section 2.2: Ordered Sets
-- ========================================================================

-- ------------------------------------------------------------------------
-- 2.2.1: Basic Properties
-- ------------------------------------------------------------------------

-- Definitions provided by Common.Closure: Reflexive, Symmetric, Transitive

-- ------------------------------------------------------------------------
-- 2.2.2: Preorders, Partial Orders, and Total Orders
-- ------------------------------------------------------------------------

-- Definitions provided by Common.Order:
-- - IsPreorder (reflexive + transitive)
-- - IsPartialOrder (preorder + antisymmetric)
-- - IsTotalOrder (partial order + total)
-- - StrictPart (< from ≤)

-- ------------------------------------------------------------------------
-- 2.2.3: Joins and Meets
-- ------------------------------------------------------------------------

-- Definitions provided by Common.Order: IsJoin, IsMeet

-- Example: 部分集合順序のハッセ図
-- Hasse diagram visualization:
--       {a,b}
--       /   \
--     {a}   {b}
--       \   /
--         ∅
-- {a} と {b} の join は {a,b}
-- {a} と {b} の meet は ∅

-- ------------------------------------------------------------------------
-- 2.2.4: Equivalence Relations
-- ------------------------------------------------------------------------

-- Definition provided by Common.Order: IsEquivalence

-- ------------------------------------------------------------------------
-- 2.2.5: Closures
-- ------------------------------------------------------------------------

-- Definitions provided by Common.Closure:
-- - IsReflexiveClosure
-- - IsTransitiveClosure
-- - IsReflTransClosure

-- ------------------------------------------------------------------------
-- Exercise 2.2.6: Reflexive Closure
-- ------------------------------------------------------------------------

-- Using Common.Closure.reflClosure and Common.Closure.reflClosure_isReflexiveClosure

example (R : Rel' α) :
    TypeSystems.IsReflexiveClosure R (TypeSystems.reflClosure R) :=
  TypeSystems.reflClosure_isReflexiveClosure R

-- ------------------------------------------------------------------------
-- Exercise 2.2.7: Transitive Closure Construction
-- ------------------------------------------------------------------------

-- Definitions provided by Common.Closure: stepTrans, Ri, transClosure

-- ------------------------------------------------------------------------
-- Exercise 2.2.8: Preservation by Reflexive-Transitive Closure
-- ------------------------------------------------------------------------

-- Using Common.Closure.RTC and Common.Closure.preservedBy_RTC

/-- 演習 2.2.8の例: Pが R で保存されるなら、R* でも保存される -/
example (P : α → Prop) (R : Rel' α) (hPR : TypeSystems.PreservedBy P R) :
    TypeSystems.PreservedBy P (TypeSystems.RTC R) :=
  TypeSystems.preservedBy_RTC P R hPR

-- ------------------------------------------------------------------------
-- 2.2.9: Chains
-- ------------------------------------------------------------------------

-- Definition provided by Common.Order: IsDecreasingChain

-- ------------------------------------------------------------------------
-- 2.2.10: Well-Foundedness
-- ------------------------------------------------------------------------

-- Definition provided by Common.Order: WellFounded

/-!
### Well-Foundedness の直感

**整礎 (Well-founded)** = 「無限に下がり続ける列が存在しない」

例：
- **OK（整礎）**: 自然数 → `3 > 2 > 1 > 0` で止まる
- **NG（非整礎）**: 整数 → `... > -3 > -4 > -5 > ...` 永遠に下がれる

重要性：
- 再帰が止まる条件
- 構造的帰納法 / well-founded recursion の基礎
-/

-- ========================================================================
-- Section 2.3: Sequences
-- ========================================================================

-- ------------------------------------------------------------------------
-- 2.3.1: Sequences and Permutations
-- ------------------------------------------------------------------------

/-- 列の定義 -/
abbrev Seq (α : Type) := List α

def seq_a : Seq Nat := [3, 2, 1]
def seq_b : Seq Nat := [5, 6]

example : Seq Nat := 0 :: seq_a  -- 先頭に追加
example : Seq Nat := seq_a ++ [0]  -- 末尾に追加
example : Seq Nat := seq_a ++ seq_b  -- 連結
example : Nat := seq_a.length  -- 長さ
example : Seq Nat := []  -- 空列

/-- 並べ替え (permutation) -/
def IsPermutation {α : Type} (xs ys : Seq α) : Prop :=
  List.Perm xs ys

-- ========================================================================
-- Section 2.4: Induction
-- ========================================================================

-- ------------------------------------------------------------------------
-- 2.4.1: Ordinary Induction on Natural Numbers
-- ------------------------------------------------------------------------

theorem ordinary_induction
    (P : Nat → Prop)
    (h0 : P 0)
    (hstep : ∀ n : Nat, P n → P (n + 1)) :
    ∀ n : Nat, P n := by
    intro n
    induction n with
    | zero => exact h0
    | succ n ih => exact hstep n ih

-- ------------------------------------------------------------------------
-- 2.4.2: Complete Induction
-- ------------------------------------------------------------------------

theorem complete_induction
    (P : Nat → Prop)
    (hstep : ∀ n : Nat, (∀ i : Nat, i < n → P i) → P n) :
    ∀ n : Nat, P n := by
    intro n
    exact Nat.strong_induction_on n hstep

-- ------------------------------------------------------------------------
-- 2.4.3: Lexicographic Order
-- ------------------------------------------------------------------------

/-- 辞書式順序 (≤ version) -/
def Lex (p q : Nat × Nat) : Prop :=
  p.1 < q.1 ∨ (p.1 = q.1 ∧ p.2 ≤ q.2)

/-- 辞書式順序 (< version) -/
def LexStrict (p q : Nat × Nat) : Prop :=
  p.1 < q.1 ∨ (p.1 = q.1 ∧ p.2 < q.2)

end Chapter02
