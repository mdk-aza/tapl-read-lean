import Mathlib.Data.Set.Basic

open Set

namespace TaPL212

variable {α : Type}

-- # 2.1.2
#check Nat

-- 可算集合の定義
-- S が可算 ⇔ Natと一対一対応がある
--  Myℕ  : Set Nat は「自然数の集合」
-- Nat : Type は「自然数の型」
-- ≃ は型どうしに使う

-- //は「条件を満たす要素だけを集めた型（Subtype）」
def isCountable (S : Set α) : Prop :=
  Nonempty (Nat ≃ {x // x ∈ S})

--∃ は、「条件を満たす要素が少なくとも1つ存在する」ことを意味する
-- ∃の例
-- ⟨値, 証明⟩
-- by decide とは？
-- 👉 Leanが自動で真偽を判定
example : ∃ x : Nat, x > 5 := by
  exact ⟨6, by decide⟩

end TaPL212