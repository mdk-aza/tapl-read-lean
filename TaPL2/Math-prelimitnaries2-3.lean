import Mathlib


open Set
open List

-- # 2.3.1
namespace TaPL231

/--
定義 2.3.1:
  列は Lean では `List α` で表す。
  -/
abbrev Seq (α : Type) := List α

def a : Seq Nat := [3, 2, 1]
def b : Seq Nat := [5, 6]

example : Seq Nat := 0 :: a -- 0,a
example : Seq Nat := a ++ [0] -- a,0
example : Seq Nat := a ++ b -- a,b

example : Nat := a.length -- |a|
example : Seq Nat := [] -- 空列

/--
並べ替え（permutation） :
  順序は違っても、同じ要素を持つ列
  -/
def IsPermutation {α : Type} (xs ys : Seq α) : Prop :=
  List.Perm xs ys

end TaPL231