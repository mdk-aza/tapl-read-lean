import Mathlib.Data.Set.Basic

open Set

namespace TaPL214

variable {α : Type}

-- # 2.1.4
-- 単項関係 = 1個の要素に対する条件

-- ① 集合として
-- P : Set α
-- 👉 条件を満たす要素の集まり
-- ② 関数として
-- P : α → Prop
-- 👉 要素を入れると「真 or 偽」を返す

-- これが核心
-- Set α = α → Prop

-- 👉 集合 = 条件（述語）
-- 単項関係 = 述語
def Predicate := α → Prop

-- 集合としての表現
variable (S : Set α)

-- s ∈ P
example (P : Set α) (s : α) : Prop :=
  s ∈ P

-- P(s) と同じ意味
example (P : α → Prop) (s : α) : Prop :=
  P s

-- 上記2つが同じことを証明
example (P : Set α) (s : α) :
    s ∈ P ↔ P s := by
  rfl

end TaPL214

