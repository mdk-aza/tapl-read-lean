import Mathlib.Data.Set.Basic

open Set

-- # 2.1.9
-- 「次に、その部分関数に対して、ある入力で値があるかどうかを定義している。
-- f(x)↓ は値が存在すること、f(x)↑ は値が存在しないこと。」

namespace TaPL219

variable {α β : Type}

/-- 関係 R の定義域 -/
def dom (R : Set (α × β)) : Set α :=
  {x | ∃ y, (x, y) ∈ R}

/--
x で定義されている
（教科書の f(x)↓ に対応）
-/
def DefinedAt (R : Set (α × β)) (x : α) : Prop :=
  x ∈ dom R

/--
x で未定義である
（教科書の f(x)↑ に対応）
-/
def UndefinedAt (R : Set (α × β)) (x : α) : Prop :=
  x ∉ dom R

theorem definedAt_iff_exists (R : Set (α × β)) (x : α) :
    DefinedAt R x ↔ ∃ y, (x, y) ∈ R := by
  rfl

theorem undefinedAt_iff_not_exists (R : Set (α × β)) (x : α) :
    UndefinedAt R x ↔ ¬ ∃ y, (x, y) ∈ R := by
  rfl

end TaPL219

