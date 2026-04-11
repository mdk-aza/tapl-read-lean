import Mathlib.Data.Set.Basic

open Set

namespace TaPL311

inductive Term : Type where
  | tmTrue : Term
  | tmFalse : Term
  | tmIf : Term → Term → Term → Term
  | tmZero : Term
  | tmSucc : Term → Term
  | tmPred : Term → Term
  | tmIsZero : Term → Term
deriving Repr

end TaPL311