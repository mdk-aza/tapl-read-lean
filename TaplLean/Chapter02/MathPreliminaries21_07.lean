import Mathlib.Data.Set.Basic

open Set

namespace TaPL217

variable {α β : Type}

-- # 2.1.7
-- 関係 R
variable (R : Set (α × β))

-- (s, t) ∈ R となる t が存在する s
-- 定義域 dom(R)
def domRel : Set α :=
  {s | ∃ t, (s, t) ∈ R}

-- (s, t) ∈ R となる s が存在する t
-- 値域 range(R)
--
-- 可視化の例
-- R:
-- a → b
-- b → c
-- dom   = {a, b}
-- range = {b, c}
def ranRel : Set β :=
  {t | ∃ s, (s, t) ∈ R}

example (s : α) :
    s ∈ domRel R ↔ ∃ t, (s, t) ∈ R := by
  rfl

example (t : β) :
    t ∈ ranRel R ↔ ∃ s, (s, t) ∈ R := by
  rfl

-- 関係 = ペアの集合
-- dom/range = 存在で定義
-- 関数 = 存在 + 一意
-- 単射/全射 = さらに条件

-- 単射（injective）
-- 「違う入力 → 違う出力」
-- 同じ y に対応する x は1つ
def isFunction (R : Set (α × β)) : Prop :=
  ∀ x y₁ y₂,
    (x, y₁) ∈ R →
    (x, y₂) ∈ R →
    y₁ = y₂

-- 全射（surjective）
-- 「すべての出力が使われる」
-- すべての y に対して対応する x がある
def isSurjective (R : Set (α × β)) (T : Set β) : Prop :=
  ∀ y ∈ T, ∃ x, (x, y) ∈ R

end TaPL217

