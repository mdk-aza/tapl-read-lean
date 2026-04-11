import Mathlib.Data.Set.Basic
import Mathlib.Tactic

open Set

-- # 2.2.1
namespace TaPL221
--  反射的（reflexive）すべての要素が「自分自身と関係を持つ」 自分と自分はOK
-- Lean、型理論らしい書き方
-- a ↺
-- b ↺
-- c ↺
def Reflexive {α} (R : α → α → Prop) : Prop :=
  ∀ x, R x x

--  対称的（symmetric）すべての要素が「互いに関係を持つ」、片方が成り立ったら、逆も成り立つ
-- Lean、型理論らしい書き方
-- a ↔ b
def Symmetric {α} (R : α → α → Prop) : Prop :=
  ∀ x y, R x y → R y x

-- 推移的（transitive）すべての要素が「推移的」、xとyが関係を持ち、yとzが関係を持ったら、xとzも関係を持つ
-- Lean、型理論らしい書き方
-- a → b → c
-- なら a → c も必要
def Transitive {α} (R : α → α → Prop) : Prop :=
  ∀ x y z, R x y → R y z → R x z

end TaPL221

-- # 2.2.2
namespace TaPL222

universe u

variable {S : Type u}

-- S 上の二項関係
abbrev Rel (S : Type u) := S → S → Prop

-- 反射的
def Reflexive (R : Rel S) : Prop :=
  ∀ s : S, R s s

-- 推移的
def Transitive (R : Rel S) : Prop :=
  ∀ ⦃s t u : S⦄, R s t → R t u → R s u

-- 反対称的
def Antisymmetric (R : Rel S) : Prop :=
  ∀ ⦃s t : S⦄, R s t → R t s → s = t

-- 全比較可能
def Total (R : Rel S) : Prop :=
  ∀ s t : S, R s t ∨ R t s

/--
定義 2.2.2 (前順序):
  `S` 上の反射的かつ推移的な関係 `R` を、`S` 上の前順序という。
  -/

--   直感

--   「並べられそうだけど、まだ区別が甘い順序」

--   同じ扱いのものが複数あってもOK
--   「順番っぽい構造」はある
--   例
--   「サイズが同じか小さい」みたいな関係
--   型システムの「サブタイプ関係（構造的型）」も前順序になることが多い

--   👉 ポイント
-- 順序っぽいけど、同じ扱いのものが区別されない

def IsPreorder (R : Rel S) : Prop :=
  Reflexive R ∧ Transitive R

/--
`R` に対応する狭義関係。
TAPL の `s < t` は `s ≤ t ∧ s ≠ t` を意味するので、
それを一般の関係 `R` に対して定義している。
-/

-- 直感

-- 「本当に小さい（イコールは除く）」

-- ≤
-- ≤：以下
-- <
-- <：未満
-- 例
-- 3
-- ≤
-- 3
-- 3≤3 は OK
-- 3
-- <
-- 3
-- 3<3 は NG

-- 👉 ポイント
-- 「等しい」を除いたバージョン

def StrictPart (R : Rel S) (s t : S) : Prop :=
  R s t ∧ s ≠ t

/--
定義 2.2.2 (半順序):
  反対称的でもある前順序を半順序という。
  -/

-- 直感

-- 「ちゃんと区別できる順序」

-- 同じ扱いだったものが、実際に同一と判定される
-- 例
-- 数の大小（≤）
-- 集合の包含関係（⊆）

-- 👉 ポイント
-- 双方向に成り立ったら「同じ」とみなす


def IsPartialOrder (R : Rel S) : Prop :=
  IsPreorder R ∧ Antisymmetric R

/--
定義 2.2.2 (全順序):
  任意の `s t : S` に対し `R s t` または `R t s` が成り立つ半順序を全順序という。
  -/


-- 直感

-- 「必ず比較できる順序（完全に並べられる）」

-- 例
-- 実数の大小
-- 自然数の大小
-- 反例（全順序じゃない）
-- 集合の包含（⊆）
-- → 比較できない場合がある（例：{1} と {2}）

-- 👉 ポイント
-- どんな2つでも必ず大小関係がつく

def IsTotalOrder (R : Rel S) : Prop :=
  IsPartialOrder R ∧ Total R


end TaPL222

-- # 2.2.3
namespace TaPL223

/-- `Rel S` は、型 `S` 上の二項関係を表す。 -/
abbrev Rel (S : Type u) := S → S → Prop

variable {S : Type u}

/-- 反射的 -/
def Reflexive (R : Rel S) : Prop :=
  ∀ s : S, R s s

/-- 推移的 -/
def Transitive (R : Rel S) : Prop :=
  ∀ ⦃s t u : S⦄, R s t → R t u → R s u

/-- 反対称的 -/
def Antisymmetric (R : Rel S) : Prop :=
  ∀ ⦃s t : S⦄, R s t → R t s → s = t

/-- 前順序 -/
def IsPreorder (R : Rel S) : Prop :=
  Reflexive R ∧ Transitive R

/-- 半順序 -/
def IsPartialOrder (R : Rel S) : Prop :=
  IsPreorder R ∧ Antisymmetric R

-- これは ハッセ図が本命で可視化しやすい。

-- 例：部分集合順序
--       {a,b}
--       /   \
--     {a}   {b}
--       \   /
--         ∅
-- {a} と {b} の join は {a,b}
-- {a} と {b} の meet は ∅

-- これが一番わかりやすいです。

/--
定義 2.2.3:
  `j` が `s` と `t` の結び (join, least upper bound) であるとは、
  `s ≤ j` かつ `t ≤ j` であり、
  さらに `s ≤ k` かつ `t ≤ k` を満たすすべての上界 `k` に対して `j ≤ k`
  が成り立つことである。
  -/
def IsJoin (R : Rel S) (s t j : S) : Prop :=
  R s j ∧
  R t j ∧
  ∀ k : S, R s k → R t k → R j k

/--
定義 2.2.3:
  `m` が `s` と `t` の交わり (meet, greatest lower bound) であるとは、
  `m ≤ s` かつ `m ≤ t` であり、
  さらに `n ≤ s` かつ `n ≤ t` を満たすすべての下界 `n` に対して `n ≤ m`
  が成り立つことである。
  -/
def IsMeet (R : Rel S) (s t m : S) : Prop :=
  R m s ∧
  R m t ∧
  ∀ n : S, R n s → R n t → R n m

end TaPL223

-- # 2.2.4
namespace TaPL224

/-- `Rel S` は型 `S` 上の二項関係を表す。 -/
abbrev Rel (S : Type u) := S → S → Prop

variable {S : Type u}

/-- 反射的 -/
def Reflexive (R : Rel S) : Prop :=
  ∀ s : S, R s s

/-- 推移的 -/
def Transitive (R : Rel S) : Prop :=
  ∀ ⦃s t u : S⦄, R s t → R t u → R s u

/-- 対称的 -/
def Symmetric (R : Rel S) : Prop :=
  ∀ ⦃s t : S⦄, R s t → R t s

/--
定義 2.2.4:
  `S` 上の反射的・対称的・推移的な関係を同値関係という。
  -/
def IsEquivalence (R : Rel S) : Prop :=
  Reflexive R ∧ Symmetric R ∧ Transitive R


end TaPL224


-- # 2.2.5
-- TAPLの「最小」は、
-- 他のどの候補 R'' よりも小さい（包含される）
-- 研究的に重要な視点
-- この定義は実は
-- 👉 帰納的定義（inductive）と同値

namespace TaPL225

/-- `Rel S` は型 `S` 上の二項関係を表す。 -/
abbrev Rel (S : Type u) := S → S → Prop

variable {S : Type u}

/-- 関係の包含 `R ⊆ R'` -/
def SubRel (R R' : Rel S) : Prop :=
  ∀ ⦃s t : S⦄, R s t → R' s t

  infix:50 " ⊆r " => SubRel

/-- 反射的 -/
def Reflexive (R : Rel S) : Prop :=
  ∀ s : S, R s s

/-- 推移的 -/
def Transitive (R : Rel S) : Prop :=
  ∀ ⦃s t u : S⦄, R s t → R t u → R s u

/--
定義 2.2.5:
  R の反射的閉包とは、R を含む最小の反射的関係である。
  -/
  -- 👉 「足りない self-loop を全部足す」
def IsReflexiveClosure (R R' : Rel S) : Prop :=
  SubRel R R' ∧
  Reflexive R' ∧
  ∀ R'' : Rel S,
    SubRel R R'' →
    Reflexive R'' →
    SubRel R' R''

/--
定義 2.2.5:
  R の推移的閉包とは、R を含む最小の推移的関係である。
  -/
  -- 👉 「経路を全部つなぐ」
def IsTransitiveClosure (R R' : Rel S) : Prop :=
  SubRel R R' ∧
  Transitive R' ∧
  ∀ R'' : Rel S,
    SubRel R R'' →
    Transitive R'' →
    SubRel R' R''

/--
定義 2.2.5:
  R の反射的推移的閉包とは、R を含む最小の反射的かつ推移的な関係である。
  （R* に対応）
  -/
  --   👉 「自己ループ + 経路全部」
  -- これは
  -- 👉 グラフの到達可能性（reachability）

def IsReflTransClosure (R R' : Rel S) : Prop :=
  SubRel R R' ∧
  Reflexive R' ∧
  Transitive R' ∧
  ∀ R'' : Rel S,
    SubRel R R'' →
    Reflexive R'' →
    Transitive R'' →
    SubRel R' R''

end TaPL225

-- # 2.2.6
namespace TaPL226
universe u

/-- `Rel S` は型 `S` 上の二項関係を表す。 -/
abbrev Rel (S : Type u) := S → S → Prop

variable {S : Type u}

/-- 関係の包含 `R ⊆ R'` -/
def SubRel (R R' : Rel S) : Prop :=
  ∀ ⦃s t : S⦄, R s t → R' s t

  infix:50 " ⊆r " => SubRel

/-- 反射的 -/
def Reflexive (R : Rel S) : Prop :=
  ∀ s : S, R s s

/--
`R'` が `R` の反射的閉包であるとは、
`R` を含む最小の反射的関係であることをいう。
-/
def IsReflexiveClosure (R R' : Rel S) : Prop :=
  SubRel R R' ∧
  Reflexive R' ∧
  ∀ R'' : Rel S,
    SubRel R R'' →
    Reflexive R'' →
    SubRel R' R''

/--
`reflClosure R` は、`R` にすべての `(s,s)` を加えた関係。
TAPL の
`R' = R ∪ {(s,s) | s ∈ S}`
に対応する。
-/
def reflClosure (R : Rel S) : Rel S :=
  fun s t => R s t ∨ s = t

-- R' は
-- ・R を含む
-- ・反射的
-- ・最小

/--
演習 2.2.6:
  `reflClosure R` は `R` の反射的閉包である。
  -/
theorem reflClosure_isReflexiveClosure (R : Rel S) :
    IsReflexiveClosure R (reflClosure R) :=
    ⟨
      -- R ⊆ R'
    (fun {_ _} h => Or.inl h),
    -- R' は反射的
    (fun s => Or.inr rfl),
    --  R'' が
    --    ・R を含む
    --    ・反射的
    -- なら
    -- R' ⊆ R''
    (fun R'' hRR'' hRefl {_ _} h =>
      Or.elim h
        (fun hR => hRR'' hR)
        (fun hEq =>
          Eq.ndrec (hRefl _) hEq))
        ⟩


end TaPL226


-- # 2.2.7
namespace TaPL227

abbrev Rel (S : Type u) := S → S → Prop

variable {S : Type u}

/-- 関係の包含 -/
def SubRel (R R' : Rel S) : Prop :=
  ∀ ⦃s t : S⦄, R s t → R' s t

/-- 推移的 -/
def Transitive (R : Rel S) : Prop :=
  ∀ ⦃s t u : S⦄, R s t → R t u → R s u

/--
`stepTrans R'` は、関係 `R'` に
「1段階の推移で得られる辺」を加えたもの。
-/
def stepTrans (R' : Rel S) : Rel S :=
  fun s u =>
    R' s u ∨ ∃ t : S, R' s t ∧ R' t u

/--
演習 2.2.7 の `R_i`
- `R_0 = R`
- `R_{i+1} = R_i ∪ { (s,u) | ∃ t, (s,t) ∈ R_i ∧ (t,u) ∈ R_i }`
-/
def Ri (R : Rel S) : Nat → Rel S
| 0 => R
| n + 1 => stepTrans (Ri R n)

/--
演習 2.2.7 の `R⁺`
`R⁺ s t` とは、ある段階 `i` で `R_i s t` が成り立つこと。
-/
def transClosure (R : Rel S) : Rel S :=
  fun s t => ∃ i : Nat, Ri R i s t

end TaPL227


-- # 2.2.8

-- 2.2.8 は、R* を“帰納的に”持ってくると急に証明しやすくなる
-- というのが核心です。

-- なので輪読では、

-- 2.2.5 では「最小性」で定義
-- 2.2.8 では「構成的 / 帰納的定義」に切り替える

-- と説明するとかなり自然です。

namespace TaPL228

abbrev Rel (S : Type u) := S → S → Prop

variable {S : Type u}

/-- `P` が関係 `R` によって保存されること -/
def PreservedBy (P : S → Prop) (R : Rel S) : Prop :=
  ∀ ⦃s t : S⦄, R s t → P s → P t

/--
`RTC R` は `R` の反射的推移的閉包 (`R*`)。
-/
-- RTC
-- これは R* のことです。
-- 意味は：
-- * refl
--   s R* s が成り立つ
-- * tail
--   s R t と t R* u があれば s R* u

-- つまり、R を何回かたどって行けるなら R に入る*、という定義です。
inductive RTC (R : Rel S) : Rel S
| refl : ∀ s : S, RTC R s s
| tail : ∀ {s t u : S}, R s t → RTC R t u → RTC R s u

/--
`P` が `R` によって保存されるなら、`P` は `R*` によっても保存される。
（演習 2.2.8）
-/


theorem preservedBy_RTC
-- これは

-- 仮定：P は R で保存される
-- 結論：P は RTC R でも保存される

-- という意味です。
    (P : S → Prop)
    (R : Rel S)
    (hPR : PreservedBy P R) :
    PreservedBy P (RTC R) := by
    -- いま
    -- hst : RTC R s t
    -- hPs : P s
    -- を仮定して、P t を示したいです。
    -- そこで hst に対して帰納法します。
    intro s t hst hPs
    induction hst with
      --     この場合は t = s なので、示すべき P t はそのまま P s。
      -- もう hPs : P s を持っているので終わりです。
    | refl s =>
      exact hPs
    | tail hR hRTC ih =>
      exact ih (hPR hR hPs)

end TaPL228

-- # 2.2.9
namespace TaPL229

-- 「ずっと下がり続ける列」
-- 「終わりなく、小さくなり続ける並び」
-- なぜ重要？

-- 超シンプルまとめ

-- 👉 「無限に下がり続けるチェーン」

-- 次の定義（well-founded）で出てきます：

-- 👉 「こんな列が存在しない」＝良い構造

/-- 型 `S` 上の二項関係 -/
abbrev Rel (S : Type u) := S → S → Prop

variable {S : Type u}

/-- 狭義関係: `s < t` は `s ≤ t ∧ s ≠ t` -/
def StrictPart (R : Rel S) (s t : S) : Prop :=
  R s t ∧ s ≠ t

/-- 定義 2.2.9: 降下列 -/
def IsDecreasingChain (R : Rel S) (c : Nat → S) : Prop :=
  ∀ i : Nat, StrictPart R (c (i + 1)) (c i)

end TaPL229

-- # 2.2.10
namespace TaPL2210

-- OK（整礎）

-- 自然数：

-- 3 > 2 > 1 > 0 → ここで止まる

-- 👉 無限に下がれない


-- NG（非整礎）

-- 整数：

-- ... > -3 > -4 > -5 > ...

-- 👉 永遠に下がれる

-- ここが超重要（理解ポイント）

-- 👉 「底があるかどうか」

-- 自然数 → 底がある（0）
-- 整数 → 底がない

-- 研究的に重要な意味

-- これめちゃくちゃ重要です：

-- 👉 再帰が止まる条件

-- well-founded ⇒ 再帰OK
-- 非well-founded ⇒ 無限ループ可能

-- 次につながる話（重要）

-- この後出てくる：

-- 👉 構造的帰納法 / well-founded recursion

-- は全部これに依存します

-- 整礎（well-founded）＝「無限に下がり続ける列が存在しない」
abbrev Rel (S : Type u) := S → S → Prop

variable {S : Type u}

/-- 狭義関係 -/
def StrictPart (R : Rel S) (s t : S) : Prop :=
  R s t ∧ s ≠ t

/-- 降下列 -/
def IsDecreasingChain (R : Rel S) (c : Nat → S) : Prop :=
  ∀ i : Nat, StrictPart R (c (i + 1)) (c i)

/--
定義 2.2.10:
  無限降下列が存在しないとき、R は整礎である
  -/
def WellFounded (R : Rel S) : Prop :=
  ¬ ∃ c : Nat → S, IsDecreasingChain R c


end TaPL2210