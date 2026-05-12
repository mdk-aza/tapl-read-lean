namespace TypeSystemsInLean.TaPL.Chapter03

inductive Term where
  | tru
  | fls
  | if_    : Term → Term → Term → Term
  | zero
  | succ   : Term → Term
  | pred   : Term → Term
  | iszero : Term → Term
deriving DecidableEq, Repr
-- DecidableEq「等しいかどうかを機械的に判定できる型」 true か false か -計算で決められる
-- ないとt1 = t2はただの論理命題

open Term

/-- numeric values -/
inductive NumericValue : Term → Prop where
  | zero : NumericValue zero
  | succ : NumericValue t → NumericValue (succ t)

/-- values -/
inductive Value : Term → Prop where
  | tru  : Value tru
  | fls  : Value fls
  | num  : NumericValue t → Value t

/-- standard one-step semantics for Chapter 3 arithmetic terms -/
inductive Step : Term → Term → Prop where
  | ifTrue  : Step (if_ tru  t2 t3) t2
  | ifFalse : Step (if_ fls  t2 t3) t3
  | ifCong  : Step t1 t1' →
              Step (if_ t1 t2 t3) (if_ t1' t2 t3)

  | succCong : Step t1 t1' →
               Step (succ t1) (succ t1')

  | predZero : Step (pred zero) zero
  | predSucc : NumericValue nv →
               Step (pred (succ nv)) nv
  | predCong : Step t1 t1' →
               Step (pred t1) (pred t1')

  | iszeroZero : Step (iszero zero) tru
  | iszeroSucc : NumericValue nv →
                 Step (iszero (succ nv)) fls
  | iszeroCong : Step t1 t1' →
                 Step (iszero t1) (iszero t1')

/-- normal form -/
-- 「tから1ステップも進めない」¬ が否定
def NormalForm (R : Term → Term → Prop) (t : Term) : Prop :=
  ¬ ∃ t', R t t'

/-- reflexive-transitive closure -/
inductive MultiStep (R : α → α → Prop) : α → α → Prop where
  | refl  : MultiStep R t t
  | trans : R t u → MultiStep R u v → MultiStep R t v

/-- a closed term is stuck if it is a normal form but not a value -/
-- 「これ以上評価できないのに、値でもない状態」
-- ¬ Value t 正しい値ではない
def Stuck (R : Term → Term → Prop) (t : Term) : Prop :=
  NormalForm R t ∧ ¬ Value t

end TypeSystemsInLean.TaPL.Chapter03