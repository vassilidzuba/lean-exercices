import Mathlib

section one

/- exercice from Mathematics in Lean -/

theorem my_lemma4 :
  ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε := by
  intro x y ε epos ele1 xlt ylt
  have ha : |x| ≤ ε := by
     apply le_of_lt
     apply xlt
  have hb : |y| ≤ ε := by
     apply le_of_lt
     apply ylt
  calc
  |x * y| = |x| * |y| := by apply abs_mul
  _ ≤ |x| * ε := by
    apply mul_le_mul
    · rfl
    · apply hb
    · apply abs_nonneg
    · apply abs_nonneg
  _ < 1 * ε := by
    rw [mul_lt_mul_right]
    · apply lt_of_lt_of_le
      · apply xlt
      · apply ele1
    · apply epos
  _ = ε := by apply one_mul

#check my_lemma4


end one
