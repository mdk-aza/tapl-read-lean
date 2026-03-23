import Mathlib.Data.Set.Basic

open Set

-- # 2.1.3
-- 関係とは「組（タプル）の集合」
-- 関係 = 全組み合わせの中から好きなものを選んだ集合
-- 関係 = 「OKな組のリスト」

namespace TaPL213

variable {α₁ α₂ : Type}

-- 2項関係（n=2 の場合）
-- R ⊆ S₁ × S₂
-- ×ˢは集合の直積（set product）
-- S₁ × S₂ = {(x, y) | x ∈ S₁ ∧ y ∈ S₂}
-- R : Set (α × β)はペアの集合
-- 関係付けられる→(x, y) ∈ R
-- 関係 = 条件
-- x < yも関係
-- R := { (x, y) | x < y } は条件を満たすペアだけを集めたもの


-- //は「条件を満たす要素だけを集めた型（Subtype）」
def Rel₂ (S₁ : Set α₁) (S₂ : Set α₂) :=
  {R : Set (α₁ × α₂) // R ⊆ (S₁ ×ˢ S₂)}

end TaPL213