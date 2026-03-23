import Mathlib.Data.Set.Basic

open Set

-- # 2.1.10
-- 👉 「関係で1ステップ進んでも性質が壊れない」
-- 👉「R は状態遷移、P は性質だと見ると、
-- R によって P が保存されるとは、
-- 1ステップ遷移しても P が成り立ち続けること。」

namespace TaPL2110

variable {α : Type}

-- R : α → α → Prop
-- 👉 二項関係（2.1.5）
-- P : α → Prop
-- 👉 述語（2.1.4）

/--
S 上の二項関係 R と述語 P に対して、
P が R によって保存される
-/
def PreservedBy (R : α → α → Prop) (P : α → Prop) : Prop :=
  ∀ s s', R s s' → P s → P s'

-- 教科書忠実
def PreservedBySet (R : Set (α × α)) (P : α → Prop) : Prop :=
  ∀ s s', (s, s') ∈ R → P s → P s'

end TaPL2110

