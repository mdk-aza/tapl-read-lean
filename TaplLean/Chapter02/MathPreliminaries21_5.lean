import Mathlib.Data.Set.Basic

open Set

-- # 2.1.5
-- 前半
-- (s, t) ∈ R の代わりに s R t と書く
-- 👉 ただの書き換え（記法の省略）

-- 後半
-- S = T = U のとき、U 上の二項関係
-- 👉 同じ集合内の関係（自己関係）

namespace TaPL215

variable {α β : Type}

-- 関係（集合として）
def R : Set (α × β) := Set.univ

-- 数学	(s, t) ∈ R -- Lean (s, t) ∈ R
example (R : Set (α × β)) (s : α) (t : β) : Prop :=
  (s, t) ∈ R

def Rel (α β : Type) := α → β → Prop

variable (R : α → β → Prop)

-- 数学 s R t-- Lean R s t
example (s : α) (t : β) : Prop :=
  R s t

end TaPL215

