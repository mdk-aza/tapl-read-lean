import Mathlib.Data.Set.Basic

open Set

-- 定義2.1.8
-- 「まず関数を“関係の一種”として定義している。
-- 部分関数は、同じ入力に対して出力が高々1つの関係。
-- 全域関数は、さらに全ての入力で値があるもの。」

namespace TaPL218

variable {α β : Type}

/-- 関係 R の定義域 -/
def dom (R : Set (α × β)) : Set α :=
  {x | ∃ y, (x, y) ∈ R}

/--
S から T への部分関数：
R は S × T の部分集合であり、
同じ入力に対して出力は高々1つ
-/
def IsPartialFunction (S : Set α) (T : Set β) (R : Set (α × β)) : Prop :=
  R ⊆ (S ×ˢ T) ∧
  ∀ x y₁ y₂,
    (x, y₁) ∈ R →
    (x, y₂) ∈ R →
    y₁ = y₂

/--
S から T への全域関数：
部分関数であり、定義域が S 全体
-/
def IsTotalFunction (S : Set α) (T : Set β) (R : Set (α × β)) : Prop :=
  IsPartialFunction S T R ∧ dom R = S

/--
同値な書き方：
各 x ∈ S に対して、対応する y がただ1つ存在する
-/
def IsTotalFunction' (S : Set α) (T : Set β) (R : Set (α × β)) : Prop :=
  R ⊆ (S ×ˢ T) ∧
  ∀ x, x ∈ S → ∃! y, (x, y) ∈ R

end TaPL218

