import Mathlib.Data.Set.Basic

open Set

-- # 2.1.6
-- Γ : コンテキスト
-- s : 項
-- T : 型
-- 意味 は三項関係
-- 見た目 は混置記法

namespace TaPL216

variable {Ctx Term Ty : Type}

-- 三つ組 (Γ, s, T) が型付け関係に入る
-- Typing → 中身（意味・定義）
def Typing : Ctx → Term → Ty → Prop :=
  fun _ _ _ => True

--  Lean では、
-- 三項関係は普通 Ctx → Term → Ty → Prop で書く
-- のが自然です。

-- notation → 見た目（書き方のルール）
--数字が大きいほど「結びつきが強い」
-- 「= と同じくらいの強さ」、式の優先度
-- 記号	優先順位（目安）
-- →	25
-- =	50
-- +	65
-- *	70
notation:50 Γ " ⊢ " s " : " T => Typing Γ s T

example (_Γ : Ctx) (_s : Term) (_T : Ty) :
    (_Γ ⊢ _s : _T) ↔ Typing _Γ _s _T := by
  rfl

end TaPL216

