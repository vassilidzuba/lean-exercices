import Mathlib

open Nat

/- example 0.3.7 : 2^(n-1) < n! -/


def fact (a : ℕ) : Nat :=
   match a with
  | zero => 1
  | succ n => (n + 1) * fact n


def pow (a b : ℕ) : Nat :=
   match b with
   | zero => 1
   | succ n => a * pow a n


lemma le_le_mul_mul (a b c d : ℕ) (h1 : a ≤ b) (h2 : c ≤ d) : a * c ≤ b * d := by
   have h3  : a * c ≤ b * c := by
      apply Nat.mul_le_mul_right
      · apply h1
   have h4  : b * c ≤ b * d := by
      apply Nat.mul_le_mul_left
      · apply h2
   apply le_trans
   · apply h3
   · apply h4

theorem ex_0_3_7 (n : ℕ) :
       pow 2 n <= fact (n + 1) := by
   induction n with
   | zero =>
       rw [pow]
       rw [fact]
       simp
       rw [fact]
   | succ n ih =>
       rw [pow]
       rw [fact]
       have h1 (n : ℕ) : 2 <= n + 1 + 1 := by simp
       apply le_le_mul_mul
       · apply h1
       · apply ih
