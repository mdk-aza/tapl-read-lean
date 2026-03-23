import Mathlib

namespace TaPL24

/-
2.4.1 自然数の通常の帰納法
-/
theorem ordinary_induction
    (P : Nat → Prop)
    (h0 : P 0)
    (hstep : ∀ n : Nat, P n → P (n + 1)) :
    ∀ n : Nat, P n := by
    intro n
    induction n with
    | zero =>
      exact h0
    | succ n ih =>
      exact hstep n ih

/-
2.4.2 自然数の完全帰納法
-/
theorem complete_induction
    (P : Nat → Prop)
    (hstep : ∀ n : Nat, (∀ i : Nat, i < n → P i) → P n) :
    ∀ n : Nat, P n := by
    intro n
    exact Nat.strong_induction_on n hstep

/-
2.4.3 辞書式順序
(m, n) ≤ (m', n') : ⇔ m < m' または (m = m' かつ n ≤ n')
-/
def Lex (p q : Nat × Nat) : Prop :=
  p.1 < q.1 ∨ (p.1 = q.1 ∧ p.2 ≤ q.2)

/-
厳密版の辞書式順序
(m, n) < (m', n') : ⇔ m < m' または (m = m' かつ n < n')
-/
def LexStrict (p q : Nat × Nat) : Prop :=
  p.1 < q.1 ∨ (p.1 = q.1 ∧ p.2 < q.2)


end TaPL24