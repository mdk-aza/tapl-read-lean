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

-- #2.1.1
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
-- シンタックスシュガー
example (S T : Set α) : Set α := S \ T

-- S:  ○ ○ ○
-- T:    ○
-- -----------
-- S\T: ○   ○

example (S T : Set α) :
    S \ T = {x | x ∈ S ∧ x ∉ T} := by
    rfl

/- べき集合 𝒫(S) -/
#check Set.powerset

-- シンタックスシュガー
example (S : Set α) : Set (Set α) := Set.powerset S
example (S : Set α) :
    Set.powerset S = {T | T ⊆ S} := by
    rfl
    -- ∀ ターンエーは全てのもの
example (S : Set α) :
    Set.powerset S = {T | ∀ x, x ∈ T → x ∈ S} := by
    rfl

-- # 2.1.2
#check Nat

-- univはその型に属するすべての要素を含む集合（＝全集合）
def Myℕ : Set Nat := Set.univ

-- 可算集合の定義
-- S が可算 ⇔ Natと一対一対応がある
--  Myℕ  : Set Nat は「自然数の集合」
-- Nat : Type は「自然数の型」
-- ≃ は型どうしに使う

-- //は「条件を満たす要素だけを集めた型（Subtype）」
def isCountable (S : Set α) : Prop :=
  Nonempty (Nat ≃ {x // x ∈ S})

-- 警告が出る例
-- def isCountable2 (S : Set α) : Prop :=
--   ∃ f : Myℕ ≃ {x // x ∈ S}, True

--∃ は、「条件を満たす要素が少なくとも1つ存在する」ことを意味する
-- ∃の例
-- ⟨値, 証明⟩
-- by decide とは？
-- 👉 Leanが自動で真偽を判定
example : ∃ x : Nat, x > 5 := by
  exact ⟨6, by decide⟩


-- # 2.1.3
-- 関係とは「組（タプル）の集合」
-- 関係 = 全組み合わせの中から好きなものを選んだ集合
-- 関係 = 「OKな組のリスト」
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


-- 可視化
-- グラフ
-- a → b
-- b → c
-- 表
--     b c
-- a   ○ ×
-- b   × ○

-- //は「条件を満たす要素だけを集めた型（Subtype）」
def Rel₂ (S₁ : Set α₁) (S₂ : Set α₂) :=
  {R : Set (α₁ × α₂) // R ⊆ (S₁ ×ˢ S₂)}


-- # 2.1.4
-- 単項関係 = 1個の要素に対する条件

-- ① 集合として
-- P : Set α

-- 👉 条件を満たす要素の集まり

-- ② 関数として
-- P : α → Prop

-- 👉 要素を入れると「真 or 偽」を返す

-- これが核心
-- Set α = α → Prop

-- 👉 集合 = 条件（述語）


-- 単項関係 = 述語
def Predicate := α → Prop

-- 集合としての表現
variable (S : Set α)

-- s ∈ P
example (P : Set α) (s : α) : Prop :=
  s ∈ P

-- P(s) と同じ意味
example (P : α → Prop) (s : α) : Prop :=
  P s

-- 上記2つが同じことを証明
example (P : Set α) (s : α) :
    s ∈ P ↔ P s := by
    rfl

-- # 2.1.5
-- 前半

-- (s, t) ∈ R の代わりに s R t と書く

-- 👉 ただの書き換え（記法の省略）

-- 後半

-- S = T = U のとき、U 上の二項関係

-- 👉 同じ集合内の関係（自己関係）


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

-- # 2.1.6

-- Γ : コンテキスト
-- s : 項
-- T : 型

-- 意味 は三項関係
-- 見た目 は混置記法

variable {Ctx Term Ty : Type}

-- 三つ組 (Γ, s, T) が型付け関係に入る
-- Typing → 中身（意味・定義）
def Typing : Ctx → Term → Ty → Prop :=
  fun Γ s T => True

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

example (Γ : Ctx) (s : Term) (T : Ty) :
    (Γ ⊢ s : T) ↔ Typing Γ s T := by
    rfl

-- # 2.1.7
-- 関係 R
variable (R : Set (α × β))

-- (s, t) ∈ R となる t が存在する s
-- 定義域 dom(R)
def domRel : Set α :=
  {s | ∃ t, (s, t) ∈ R}

-- (s, t) ∈ R となる s が存在する t
-- 値域 range(R)

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

-- 条件	意味
-- ∃	出力が存在
-- =	一意

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


-- 定義2.1.8
-- 「まず関数を“関係の一種”として定義している。
-- 部分関数は、同じ入力に対して出力が高々1つの関係。
-- 全域関数は、さらに全ての入力で値があるもの。」


-- 部分関数

-- 「1つの入力 x に対して、出力 y は多くても1つ」

-- つまり

-- (x, y₁) ∈ R
-- (x, y₂) ∈ R

-- なら必ず y₁ = y₂

-- です。

-- 全域関数

-- さらに

-- S のすべての要素で値がある

-- つまり dom(R) = S

-- です。

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