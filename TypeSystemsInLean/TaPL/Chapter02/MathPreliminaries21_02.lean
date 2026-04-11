import Mathlib.Data.Set.Basic

open Set

namespace TaPL212

variable {α : Type}

-- # 2.1.2

-- 可算集合の定義
-- S が可算 ⇔ Natと一対一対応がある
-- Nat : Type は「自然数の型」
-- ≃ は型どうしに使う

-- //は「条件を満たす要素だけを集めた型（Subtype）」
def isCountable (S : Set α) : Prop :=
  Nonempty (Nat ≃ {x // x ∈ S})

-- ∃      = Prop（論理）
-- Σ      = Type（依存ペア）
-- Subtype = Type（Prop付きの特別なΣ）

--∃ は、「条件を満たす要素が少なくとも1つ存在する」ことを意味する
-- ∃の例
-- ⟨値, 証明⟩
-- by decide とは？
-- 👉 Leanが自動で真偽を判定
-- 存在の証明 、主張
example : ∃ x : Nat, x > 5 := by
  exact ⟨6, by decide⟩

-- example (h : ∃ x : Nat, x > 5) : True := by
--   rcases h with ⟨x, hx⟩
--   trivial

-- 条件付きデータ、実態
example : {x // x > 5} := by
  exact ⟨6, by decide⟩

-- example (x : {x // x > 5}) : Nat := x.val

-- Lean的な違い（超重要）
-- 	∃	Subtype
-- 種類	Prop	Type
-- 目的	証明	データ
-- 取り出し	rcases	.val
-- 中身	見えない	見える


example : isCountable (Set.univ : Set Nat) := by
  refine ⟨?_⟩
  refine
    { toFun := fun n => ⟨n, by trivial⟩
      invFun := fun x => x.val
      left_inv := by intro n; rfl
      right_inv := by intro x; cases x; rfl }

end TaPL212