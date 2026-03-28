import Mathlib.Data.Set.Basic

open Set

-- 2.1で大事なこと
-- 「集合は条件、関係は対応、関数は一意な対応。
-- そしてそれらは全部“存在（∃）と条件（Prop）”で表せる」
-- 集合 = 条件
-- 関係 = 条件を満たす組
-- dom = ∃で取り出す
-- 関数 = ∃ + 一意
-- 部分関数 = ∃がない場合もある
-- 保存 = 関係で進んでも条件が保たれる

-- Leanでは、
-- Prop =「真か偽かを表すもの（命題）」
-- 証明 = Prop を作ること
-- 集合 = 条件（Propを返す関数）
-- 概念	Lean
-- 集合	α → Prop
-- 関係	α → β → Prop
-- 命題	Prop

-- Propに入るもの は、「主張全体」、“証明できるかどうか”を表す
-- x > 3        -- 条件っぽい
-- 1 + 1 = 2    -- 事実
-- ∀ x, x > 0   -- 全称命題
-- ∃ x, x > 5   -- 存在命題

-- α　要素
-- Set α　要素の集合
-- Set (Set α) 集合の集合（べき集合）

namespace TaPL211

variable {α : Type}

-- 集合 S : Set α
variable (S T : Set α) (x : α)

-- x ∈ S
-- xはSに含まれる、xはSの要素である
#check x ∈ S

/- 空集合 ∅ -/
#check (∅ : Set α)

/- 部分集合 S ⊆ T -/
example (S T : Set α) : Prop := S ⊆ T

-- 部分集合
#check S ⊆ T

/- 差集合 S \ T -/
example (S T : Set α) : Set α := S \ T

-- rflは反射律

-- S \ Tの証明
example (S T : Set α) :
    S \ T = {x | x ∈ S ∧ x ∉ T} := by
    rfl

-- 直接的な項の構成よりもタクティク（by）を使う
-- カリー・ハワード同型対応により「命題の証明」は「型の項の構成」と同じであるため、
-- 関数を書くように直接証明項を記述することも可能ですが、
-- ほとんどの場合は by に続けてタクティクを用いる方が
-- 読み書きが楽になるとされています


/- べき集合 𝒫(S) -/
#check Set.powerset

example (S : Set α) : Set (Set α) := Set.powerset S

-- 𝒫(S)の証明
example (S : Set α) :
    Set.powerset S = {T | T ⊆ S} := by
    rfl

-- ∀ ターンエーは全てのもの
example (S : Set α) :
    Set.powerset S = {T | ∀ x, x ∈ T → x ∈ S} := by
    rfl

end TaPL211