import data.real.basic

lemma sub_sq_le_abs_sq_sub (u w : ℝ) (h : 0 ≤ u ↔ 0 ≤ w) : (u - w)^2 ≤ | u^2 - w^2| :=
begin
  rw sub_sq,
  by_cases diff : (w^2 ≤ u^2),
  by_cases sign : (0 ≤ u),
  have hw : 0 ≤ w := h.1 sign,
  rw sub_add,
  apply sub_le_sub (le_refl (u^2)) _,
  rw le_sub_iff_add_le,
  rw ← mul_two,
  rw mul_comm,
  rw sq,
  rw mul_assoc,
  apply mul_le_mul_of_nonneg_left,
  rw [le_sub, sub_zero] at diff, 
  have := abs_le_abs_of_sq_le_sq diff,
  rw abs_of_nonneg hw at this,
  rw abs_of_nonneg sign at this,
  exact (mul_le_mul this (le_refl w)) hw sign,
  simp only [zero_le_one, zero_le_bit0],
  have hw : w < 0 := by {rw h at sign, exact not_le.1 sign},
  rw not_le at sign


  sorry,
  simp only [zero_le_one, zero_le_bit0],
  sorry,
end