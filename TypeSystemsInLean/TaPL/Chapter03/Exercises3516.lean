import TypeSystemsInLean.TaPL.Chapter03.Common

namespace TypeSystemsInLean.TaPL.Chapter03.Ex3516

open TypeSystemsInLean.TaPL.Chapter03

-- (1)実行時のエラーの2つの取り扱いが一致する
-- 正常系、エラーが発生した異常系を分けて考えるのがスタート
-- その上で、エラーが一致するかどうかは3.5.14にあったようにstuckに評価されることと、今回定義したwrongが一緒になれば良いはず
-- 以下、Leanで証明

-- 調べながら証明するにあたって、進行性（Progress）の証明も必要なこともわかった


-- TAPL 3.5.16: Stuck states vs. Explicit 'wrong'
set_option autoImplicit false

inductive Term where
  | ttrue  : Term
  | tfalse : Term
  | tif    : Term → Term → Term → Term
  | zero   : Term
  | succ   : Term → Term
  | pred   : Term → Term
  | iszero : Term → Term
  | wrong  : Term
  deriving Repr, DecidableEq

open Term

-- [数値の定義] 構造的帰納法の基盤となる述語
-- 「ある対象（Term）が、特定の性質を満たしているかを判定しているから述語
inductive IsNumericValue : Term → Prop where
  | nv_zero : IsNumericValue zero
  | nv_succ {t : Term} : IsNumericValue t → IsNumericValue (succ t)

-- [値の定義] 進行性の「ゴール」となる正規形
inductive IsValue : Term → Prop where
  | v_true  : IsValue ttrue
  | v_false : IsValue tfalse
  | v_nv    {t : Term} : IsNumericValue t → IsValue t
  | v_wrong : IsValue wrong

-- [エラー条件の定式化]
-- 元の体系で「行き詰まっていた」ケース（型ミスマッチ）を集合として定義
def IsBadNat (t : Term) : Prop := t = wrong ∨ t = ttrue ∨ t = tfalse
def IsBadBool (t : Term) : Prop := t = wrong ∨ IsNumericValue t

inductive Step : Term → Term → Prop where
  | s_iftrue  {t1 t2 : Term} : Step (tif ttrue t1 t2) t1
  | s_iffalse {t1 t2 : Term} : Step (tif tfalse t1 t2) t2
  | s_if      {t1 t1' t2 t3 : Term} : Step t1 t1' → Step (tif t1 t2 t3) (tif t1' t2 t3)
  | s_succ    {t t' : Term} : Step t t' → Step (succ t) (succ t')
  | s_predzero: Step (pred zero) zero
  | s_predsucc {nv : Term} : IsNumericValue nv → Step (pred (succ nv)) nv
  | s_pred    {t t' : Term} : Step t t' → Step (pred t) (pred t')
  | s_iszerozero: Step (iszero zero) ttrue
  | s_iszerosucc {nv : Term} : IsNumericValue nv → Step (iszero (succ nv)) tfalse
  | s_iszero  {t t' : Term} : Step t t' → Step (iszero t) (iszero t')
  -- 以下、3.5.16で追加された 行き詰まりを wrong へ変換する規則群
  | e_if_wrong     {v t1 t2 : Term} : IsBadBool v → IsValue v → Step (tif v t1 t2) wrong
  | e_succ_wrong   {v : Term} : IsBadNat v  → IsValue v → Step (succ v) wrong
  | e_pred_wrong   {v : Term} : IsBadNat v  → IsValue v → Step (pred v) wrong
  | e_iszero_wrong {v : Term} : IsBadNat v  → IsValue v → Step (iszero v) wrong

/--
### 定理: 進行性 (Progress)
大方針: 項 t の構造に関する構造的帰納法を用いる。
-/
theorem progress (t : Term) : IsValue t ∨ ∃ t', Step t t' := by
  induction t with
  | ttrue  => left; apply IsValue.v_true
  | tfalse => left; apply IsValue.v_false
  | wrong  => left; apply IsValue.v_wrong
  | zero   => left; apply IsValue.v_nv; constructor
  -- 2. 再帰的な項 (if, succ, pred, iszero) の検討
  | tif t1 t2 t3 ih1 _ _ =>
    right-- if項は値ではないので、必ず簡約できることを示す
    -- 帰納法の仮定 (I.H.) より、t1は値か、さらに簡約可能かのいずれか
    cases ih1 with
    | inl hv1 =>
    -- [反転 (Inversion)] t1が値なら、具体的にどの値か？で場合分け
      cases hv1 with
      | v_true  => exists t2; constructor
      | v_false => exists t3; constructor
      | v_nv hnv =>
        -- t1が数値なら、元の体系では行き詰まるが、新体系では wrong へ
        exists wrong; apply Step.e_if_wrong
        · exact Or.inr hnv
        · apply IsValue.v_nv; exact hnv
      | v_wrong =>
        exists wrong; apply Step.e_if_wrong
        · exact Or.inl rfl
        · apply IsValue.v_wrong
        -- t1が簡約中なら、全体の評価も進む (E-If)
    | inr hs1 => match hs1 with | ⟨t1', hs⟩ => exists (tif t1' t2 t3); apply Step.s_if; exact hs
  | succ t ih =>
    cases ih with
    | inl hv =>
      cases hv with
      | v_nv hnv => left; apply IsValue.v_nv; apply IsNumericValue.nv_succ; exact hnv
      | v_true  => right; exists wrong; apply Step.e_succ_wrong; exact Or.inr (Or.inl rfl); apply IsValue.v_true
      | v_false => right; exists wrong; apply Step.e_succ_wrong; exact Or.inr (Or.inr rfl); apply IsValue.v_false
      | v_wrong => right; exists wrong; apply Step.e_succ_wrong; exact Or.inl rfl; apply IsValue.v_wrong
    -- 引数が簡約中なら、全体も進む (E-Succ)
    | inr hs => right; match hs with | ⟨t', hs'⟩ => exists (succ t'); constructor; exact hs'
  -- pred, iszero も succ と同様に、「引数が正しい型か、そうでなければ wrong か」を
  -- 反転（cases hv）によって網羅的にチェックすることで進行性を示す
  | pred t ih =>
      right
      cases ih with
      | inl hv =>
        cases hv with
        | v_nv hnv =>
          cases hnv with
          | nv_zero => exists zero; constructor
          -- ここで「t_inner」などの名前を明示的に取り出す
          | nv_succ hnv' =>
            -- hnv' は「IsNumericValue t_inner」という形になっているはずです
            -- exists の後ろに、その中身の項を直接指定します
            rename_i t_inner
            exists t_inner; apply Step.s_predsucc; exact hnv'
        | v_true  => exists wrong; apply Step.e_pred_wrong; exact Or.inr (Or.inl rfl); apply IsValue.v_true
        | v_false => exists wrong; apply Step.e_pred_wrong; exact Or.inr (Or.inr rfl); apply IsValue.v_false
        | v_wrong => exists wrong; apply Step.e_pred_wrong; exact Or.inl rfl; apply IsValue.v_wrong
      | inr hs => match hs with | ⟨t', hs'⟩ => exists (pred t'); constructor; exact hs'
  | iszero t ih =>
    right
    cases ih with
    | inl hv =>
      cases hv with
      | v_nv hnv =>
        cases hnv with
        | nv_zero => exists ttrue; constructor
        | nv_succ hnv' => exists tfalse; apply Step.s_iszerosucc; exact hnv'
      | v_true  => exists wrong; apply Step.e_iszero_wrong; exact Or.inr (Or.inl rfl); apply IsValue.v_true
      | v_false => exists wrong; apply Step.e_iszero_wrong; exact Or.inr (Or.inr rfl); apply IsValue.v_false
      | v_wrong => exists wrong; apply Step.e_iszero_wrong; exact Or.inl rfl; apply IsValue.v_wrong
    | inr hs => match hs with | ⟨t', hs'⟩ => exists (iszero t'); constructor; exact hs'

--
end TypeSystemsInLean.TaPL.Chapter03.Ex3516