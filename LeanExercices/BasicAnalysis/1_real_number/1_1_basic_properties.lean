import Mathlib

section s_1_1_8

/-
  property 1.1.8 about ordered fields
-/

variable {R : Type*} [CommRing R] [PartialOrder R] [IsOrderedRing R]
variable (x y z : α)



theorem add_lt_left (x y z : R) (h1 : x < y) : x + z < y + z := by
  rw [add_lt_add_iff_right]
  apply h1

theorem add_lt_right (x y z : R) (h1 : x < y) : z + x < z + y := by
  rw [add_lt_add_iff_left]
  apply h1

theorem mul_pos_pos (x y : R) (h1 : 0 < x) (h2 : 0 < y) : 0 < x * y := by
  sorry

theorem prop_1_1_8_i (x : R) (h1 : 0 < x) : -x < 0 := by
  have h2 : -x + 0 < -x + x := by
    apply add_lt_right
    · apply h1
  calc
    -x = -x + 0 := by rw [add_zero]
    _ < -x + x := by
        apply add_lt_right
        · apply h1
    _ = 0 := by
         rw [add_comm, add_neg_cancel]

theorem prop_1_1_8_ii (x y z : R) (h1 : 0 < x) (h2 : y < z) : x * y < x * z := by
  have h3 : 0 < z - y :=
    calc
      0 = y - y := by rw [sub_self]
      _ = y + -y := by rw [sub_eq_add_neg]
      _ < z + -y := by
        apply add_lt_left
        · apply h2
      _ = z - y := by rw [sub_eq_add_neg]
  have h4 : 0 < x * (z - y) := by
    apply mul_pos_pos
    · apply h1
    · apply h3
  calc
    x * y = x * y + 0 := by rw [add_zero]
    _ < x * y + x * (z - y) := by
      apply add_lt_right
      · apply h4
    _ = x * z := by ring


theorem prop_1_1_8_iii (x y z : ℝ) (h1 : x < 0) (h2 : y < z) : x * z < x * y := by
  have h3 : 0 < z - y :=
    calc
      0 = y - y := by rw [sub_self]
      _ = y + -y := by rw [sub_eq_add_neg]
      _ < z + -y := by
        apply add_lt_left
        · apply h2
      _ = z - y := by rw [sub_eq_add_neg]
  have h4 : 0 < -x :=
    calc
      0 = x - x  := by rw [sub_self]
      _ = x + -x := by rw [sub_eq_add_neg]
      _ < 0 + -x := by
        apply add_lt_left
        · apply h1
      _ = -x := by rw [zero_add]
  have h4 : 0 < -x * (z - y) := by
    apply mul_pos_pos
    · apply h4
    · apply h3
  calc
    x * z = x * z + 0 := by rw [add_zero]
    _ < x * z + -x * (z - y) := by
      apply add_lt_right
      · apply h4
    _ = x * y := by ring


theorem prop_1_1_8_iv (x : ℝ) (h1 : x ≠ 0) : 0 < x * x := by
  sorry

theorem prop_1_1_8_v (x y : ℝ) (h1 : 0 < x) (h2 : x < y) : 1 / x > 1 / y  ∧ 1 / y > 0  := by
  sorry

theorem prop_1_1_8_vi (x y : R) (h1 : 0 < x) (h2 : x < y) : x * x < y * y  := by
  have ha : 0 < y - x := by
    calc
      0 = x - x := by rw [sub_self]
      _ = x + -x := by rw [sub_eq_add_neg]
      _ < y + -x := by
        apply add_lt_left
        · apply h2
      _ = y - x := by rw [← sub_eq_add_neg]
  have hb : 0 < y + x := by
    calc
      0 = 0 + 0 := by rw [zero_add]
      _ < x + 0 := by
        apply add_lt_left
        · apply h1
      _ < x + x := by
        apply add_lt_right
        · apply h1
      _ < x + y := by
        apply add_lt_right
        · apply h2
      _ = y + x := by rw [add_comm]
  have hc : 0 < (y - x) * (y + x) := by
    apply mul_pos_pos
    · apply ha
    · apply hb
  calc
    x * x = x * x + 0 := by rw [add_zero]
    _ < x * x + (y - x) * (y + x) := by
      apply add_lt_right
      · apply hc
    _ = y * y := by ring


theorem prop_1_1_8_vii (x y z w : ℝ) (h1 : x ≤ y) (h2 : z ≤ w) : x + z < y + w := by
  sorry


end s_1_1_8
