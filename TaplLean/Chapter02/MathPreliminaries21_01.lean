import Mathlib.Data.Set.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

-- Leanの使い方
-- ① 定義そのまま       → rfl
-- ② 計算で終わる       → decide
-- ③ 仮定を使う(関数・含意)         → intro
-- ④ 存在を扱う         → rcases
-- ⑤ 答えを置く(結論)         → exact
-- ⑥ 数学的に詰める(矛盾)     → omega / linarith

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


namespace TaPL211Concrete

/-!
2.1 の要点
- 集合 = 条件 = α → Prop
- 関係 = 条件を満たす組 = α → β → Prop
- dom = ∃ で「左側に出現するもの」を取り出す
- 関数 = 関係 + 一意性
- 部分関数 = 「値がない入力」があってもよい関数的関係
- 保存 = 関係で進んでも条件が保たれる
-/

------------------------------------------------------------------------
-- 0. 集合は「条件」
------------------------------------------------------------------------

-- 5 以下の自然数全体
def Small : Set Nat := {x | x ≤ 5}

def Even (n : Nat) : Prop := ∃ k, n = 2 * k

def EvenSet : Set Nat := {n | Even n}


-- 3 は Small に入る
example : 3 ∈ Small := by
  show 3 ≤ 5
  decide

-- 7 は Small に入らない
example : 7 ∉ Small := by
  show ¬ (7 ≤ 5)
  decide

-- 4 は EvenSet に入る
example : 4 ∈ EvenSet := by
  show Even 4
  exact ⟨2, by decide⟩

-- 3 は EvenSet に入らない
example : 3 ∉ EvenSet := by
  intro h
  --   //存在（∃）を分解している
  rcases h with ⟨k, hk⟩
  omega

------------------------------------------------------------------------
-- 1. 部分集合
------------------------------------------------------------------------

-- 「2 以下なら 5 以下」
def Tiny : Set Nat := {x | x ≤ 2}

-- example : Tiny ⊆ Small := by
--   intro x hx
--   dsimp [Tiny] at hx
--   dsimp [Small]
--   omega

-- タクティク	一言
-- dsimp	定義をそのまま展開する
-- simp	賢く簡単な形にする
-- rw	等式で置き換える
-- 方針はまずsimp、強すぎてダメならdsimp
-- dsimp、simpは「集合 → 条件」に戻してる
-- 「simp定理」＝ simp が自動で使う“書き換えルール”

example : Tiny ⊆ Small := by
  intro x hx
  simp [Tiny] at hx
  simp [Small]
  exact le_trans hx (by decide)

-- 偶数かつ 4 以下の集合
def SmallEven : Set Nat := {x | x ≤ 4 ∧ Even x}

-- SmallEven ⊆ Small
example : SmallEven ⊆ Small := by
  intro x hx
  simp [SmallEven] at hx
  simp [Small]
  --   名前付きで分解
  rcases hx with ⟨h1, h2⟩
  exact le_trans h1 (by decide)

-- rcasesを使わないなら以下のようにもかける、だが基本はrcasesを使う
--   ∧ → hx.1 / hx.2
--   le_trans = 「≤ の推移律」、≤ をつなぐ
--   直感は a ≤ b かつ b ≤ c なら a ≤ c
--   hx.1なのはle_transが欲しい型にしたい
--   exact le_trans hx.1 (by decide)

-- example : SmallEven ⊆ Small := by
--   intro x hx
--   simp [SmallEven] at hx
--   simp [Small]
--   exact le_trans hx.1 (by decide)

--   x ∈ SmallEven → x ≤ 4 ∧ Even x はLeanではペアとして使う

------------------------------------------------------------------------
-- 2. 差集合
------------------------------------------------------------------------

-- Small \ EvenSet = 「5以下かつ偶数ではないもの」
example :
    Small \ EvenSet = {x | x ∈ Small ∧ x ∉ EvenSet} := by
    rfl

-- 3 は Small \ EvenSet に入る
-- constructor = 「∧（and）を作る」
-- 論理 タクティク
-- ∧ constructor / ⟨⟩
-- ∨ left / right
-- → intro
-- ∃	use / ⟨⟩

-- refineの強み
-- ① ゴールを設計できる
-- refine ⟨_, _⟩

-- 👉 「∧だな」と即判断できる

-- ② ネストに強い
-- refine ⟨_, ⟨_, _⟩⟩

-- 👉 constructorだと地獄になる

-- ③ exactと相性が良い
-- refine le_trans ?_ ?_

-- 👉 あとは埋めるだけ

example : 3 ∈ Small \ EvenSet := by
  refine ⟨?h1, ?h2⟩
  · simp [Small]
  · intro h
    rcases h with ⟨k, hk⟩
    omega

-- show は「証明のターゲットを言い直す」、show = ゴールの明示・言い換え、「証明の方向を固定する」
-- example : 3 ∈ Small \ EvenSet := by
--   refine ⟨?h1, ?h2⟩
--   · show 3 ≤ 5
--     decide
--   · intro h
--     rcases h with ⟨k, hk⟩
--     omega


-- refineを使って、ゴールを元にかける方がおすすめだが、constructorを使ってもかける
-- example : 3 ∈ Small \ EvenSet := by
--   constructor
--   · show 3 ≤ 5
--     decide
--   · show ¬ Even 3
--     intro h
--     rcases h with ⟨k, hk⟩
--     omega

-- 4 は Small \ EvenSet に入らない
example : 4 ∉ Small \ EvenSet := by
  intro h
  exact h.2 (by
    show Even 4
    exact ⟨2, by decide⟩)

------------------------------------------------------------------------
-- 3. べき集合
------------------------------------------------------------------------

def A : Set Nat := {x | x = 0 ∨ x = 1}
def B : Set Nat := {x | x = 0}

example : Set.powerset A = {T | T ⊆ A} := by
  rfl

-- left = 「ゴールが OR（∨）のとき、左側を証明する」

-- 論理	タクティク
-- ∧	constructor / ⟨⟩
-- ∨	left / right
-- →	intro
-- ∃	use / rcases

-- B は A の部分集合なので、B ∈ powerset A
example : B ∈ Set.powerset A := by
  show B ⊆ A
  intro x hx
  --  ⊢ 「hxとゴールの両方に適用」、今のゴール
  dsimp [B, A] at hx ⊢
  left
  exact hx

-- powerset の要素は「集合」
#check (Set.powerset A : Set (Set Nat))

-- ------------------------------------------------------------------------
-- -- 4. 関係 = 組に対する条件
-- ------------------------------------------------------------------------

-- -- x から y へ 1 歩進む関係
-- def Step1 : Nat → Nat → Prop := fun x y => y = x + 1

-- -- 比較まとめ
-- -- 	Step1 2 3	¬ Step1 2 4
-- -- 展開後	3 = 3	¬ (4 = 3)
-- -- 状態	自明な真	計算が必要
-- -- タクティク	dsimpで終了	decideが必要

-- -- 2 から 3 へは Step1 で進める
-- example : Step1 2 3 := by
--   dsimp [Step1]

-- -- 「関係を展開したら、ただの等式になる」と見えるから、このケースはdsimpの方が良い
-- -- example : Step1 2 3 := by
-- --   rfl

-- -- 偽（否定） → decide が必要
-- -- 2 から 4 へは Step1 で進めない
-- example : ¬ Step1 2 4 := by
--   dsimp [Step1]
--   decide

-- ------------------------------------------------------------------------
-- -- 5. dom = ∃ で取り出す
-- ------------------------------------------------------------------------

-- def dom {α β : Type} (R : α → β → Prop) : Set α :=
--   {x | ∃ y, R x y}

-- -- Step1 の定義域には 10 が入る
-- -- （なぜなら 11 を取れば Step1 10 11）
-- example : 10 ∈ dom Step1 := by
--   show ∃ y, Step1 10 y
--   refine ⟨11, ?_⟩
--   dsimp [Step1]
--   decide

-- ------------------------------------------------------------------------
-- -- 6. 関数 = 関係 + 一意性
-- ------------------------------------------------------------------------

-- -- succ 関係: y = x + 1
-- def SuccRel : Nat → Nat → Prop := fun x y => y = x + 1

-- -- 「x に対して y は一意」
-- theorem SuccRel_unique :
--     ∀ x y1 y2, SuccRel x y1 → SuccRel x y2 → y1 = y2 := by
--     intro x y1 y2 h1 h2
--     dsimp [SuccRel] at h1 h2
--     rw [h1, h2]

-- -- existence もある
-- theorem SuccRel_exists : ∀ x, ∃ y, SuccRel x y := by
--   intro x
--   refine ⟨x + 1, ?_⟩
--   dsimp [SuccRel]

-- -- つまり SuccRel は「全関数的」な関係
-- theorem SuccRel_total_function :
--     ∀ x, ∃! y, SuccRel x y := by
--     intro x
--     refine ⟨x + 1, ?_, ?_⟩
--     · dsimp [SuccRel]
--     · intro y hy
--     dsimp [SuccRel] at hy
--     exact hy.symm

-- ------------------------------------------------------------------------
-- -- 7. 部分関数 = 値がない入力があってもよいが、一意ではある
-- ------------------------------------------------------------------------

-- -- predecessor 的な関係
-- -- x ≠ 0 のときだけ、y = x - 1
-- def PredRel : Nat → Nat → Prop := fun x y => x ≠ 0 ∧ y = x - 1

-- -- 一意性はある
-- theorem PredRel_unique :
--     ∀ x y1 y2, PredRel x y1 → PredRel x y2 → y1 = y2 := by
--     intro x y1 y2 h1 h2
--     rcases h1 with ⟨_, h1eq⟩
--     rcases h2 with ⟨_, h2eq⟩
--     rw [h1eq, h2eq]

-- -- 0 には値がない
-- example : ¬ ∃ y, PredRel 0 y := by
--   intro h
--   rcases h with ⟨y, hy⟩
--   exact hy.1 rfl

-- -- 5 には値がある
-- example : ∃ y, PredRel 5 y := by
--   refine ⟨4, ?_⟩
--   constructor
--   · decide
--   · decide

-- ------------------------------------------------------------------------
-- -- 8. 保存 = 関係で進んでも条件が保たれる
-- ------------------------------------------------------------------------

-- -- 2 歩進む関係
-- def Step2 : Nat → Nat → Prop := fun x y => y = x + 2

-- -- 偶数は 2 歩進んでも偶数のまま
-- theorem even_preserved_by_Step2 :
--     ∀ x y, x ∈ EvenSet → Step2 x y → y ∈ EvenSet := by
--     intro x y hx hstep
--     rcases hx with ⟨k, hk⟩
--     dsimp [Step2] at hstep
--     dsimp [EvenSet]
--     refine ⟨k + 1, ?_⟩
--     rw [hstep, hk]
--     ring

-- ------------------------------------------------------------------------
-- -- 9. 「集合」「関係」「関数」を全部 Prop で見る
-- ------------------------------------------------------------------------

-- #check Set Nat -- Nat → Prop と同じ発想
-- #check Nat → Nat → Prop
-- #check Prop

-- -- 集合は「要素を入れると命題が返るもの」
-- example : Set Nat := fun x => x ≤ 3

-- -- 関係は「2つ入れると命題が返るもの」
-- example : Nat → Nat → Prop := fun x y => y = x + 1

end TaPL211Concrete