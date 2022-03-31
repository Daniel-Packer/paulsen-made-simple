import data.real.basic
import data.fin.basic
import summation
import algebra.big_operators.ring
import summation

variables {d n : ℕ} {hdzero : d ≠ 0}

open_locale big_operators

-- ∀ j ≤ d, ∑ (i < j), x i ≤ ∑ (i < j), y i
def majorizes_le (x y : fin d → ℝ) : Prop :=
  ∀ j ≤ d, ∑ i : (fin j), x (fin.cast_le H i) ≤ ∑ i : (fin j), y (fin.cast_le H i)

-- ∑ (i < d), x i = ∑ (i < d), y i
def majorizes_eq (x y : fin d → ℝ) : Prop :=
  ∑ i : fin d, x i = ∑ i : fin d, y i
  
def majorizes (x y : fin d → ℝ ) : Prop :=
  majorizes_le x y ∧ majorizes_eq x y

-- T x y := ∑ (j < d), j • (x j - y j)
def T (x y : fin d → ℝ) : ℝ :=
  ∑ j : fin d, (j.val + 1) • (y j - x j)

lemma T_apply' [has_zero (fin (d + 1))] {x y : fin (d + 1) → ℝ} : T x y = ∑ j i : fin (d + 1), ite (i ≤ j) (y j - x j) 0 :=
begin
  rw T,
  congr,
  ext j,
  rw finset.sum_ite,
  have : ∀ i : fin (d + 1), i ∈ finset.univ.filter (λ x : fin (d + 1), ¬x ≤ j) → (0 : ℝ) = 0 :=
  begin
    intros i h,
    exact rfl,
  end,

  have hsum := finset.sum_eq_zero this,
  simp_rw function.comp_app at hsum,
  rw [hsum, add_zero],
  rw finset.sum_const,
  simp only [fin.val_eq_coe, nsmul_eq_mul, nat.cast_add, nat.cast_one, mul_eq_mul_right_iff],
  left,
  simp_rw [fin.le_def, ← fin.coe_eq_val],
  induction ↑j with j h,
  simp_rw nat.le_zero_iff,
  have : ∀ x : fin (d + 1), ↑x = 0 ↔ x = 0 :=
  begin
    intro x,
    have : (0 : fin (d + 1)).val = 0 :=
    begin
      simp?,
    end,
  end,
  rw ← fintype.card_subtype,

  -- have : {x : fin d // ↑x = 0} ≃ {x : fin d // x = 0} :=
  -- {
  --   to_fun := 
  --   begin
  --     intro x,
  --     have := subtype.prop x,
  --     have : x = 0 := sorry,
  --   end,
  --   inv_fun :=
  --   begin

  --   end,
  --   left_inv :=
  --   begin

  --   end,
  --   right_inv :=
  --   begin

  --   end,
  -- }


  -- change ↑0 + 1 = ↑((finset.univ.filter (eq 0)).card,
  -- rw finset.filter_eq,
  -- induction j with j hj h,

  -- rw finset.sum_comm,
end

lemma T_apply {x y : fin d → ℝ} : 
  -- T x y = ∑ j : fin d, (∑ i : fin (j.val), (x (fin.cast_le j.is_lt i) - y (fin.cast_le j.is_lt i))) :=
  T x y = ∑ j : fin d, (∑ i : fin d in finset.univ.filter (λ i, i ≤ j), (x i - y i)) :=
begin
  rw T,
  induction d with d hd,
  simp only [finset.sum_sub_distrib,
 fin.val_eq_coe,
 finset.sum_empty,
 finset.filter_true_of_mem,
 nsmul_eq_mul,
 eq_self_iff_true,
 sub_zero,
 nat.cast_add,
 nat.cast_one,
 finset.sum_const_zero,
 finset.sum_congr,
 fintype.univ_of_is_empty],
  rw sum_split_last,
  rw sum_split_last,
  have : ∑ (j : fin d), (j.val + 1) • (y j - x j) = ∑ (i : fin d), ((i : fin d.succ).val + 1) • (y i - x i) :=
  begin
    sorry,
  end,
  rw ← this,
  rw hd,
  simp?,

  -- simp?,
  -- simp_rw hd,
  -- simp [hd],
  -- rw hd,
  sorry,
end

lemma eq₁ {d : ℕ} {x y : fin d → ℝ} (hmaj : majorizes x y) : 
  T x y = ∑ j : fin (d - 1), (∑ i : fin j, 
    (x (fin.cast_le (le_trans (le_of_lt j.is_lt) (nat.sub_le d 1)) i) 
      - y (fin.cast_le (le_trans (le_of_lt j.is_lt) (nat.sub_le d 1)) i))) :=
begin
  rw T_apply hmaj,
  -- Maybe Hans knows how to manipulate these sorts of results
  -- rw finset.sum_eq_add_sum_diff_singleton (d - 1 ∈ (fin d).univ),
  sorry,
end

lemma eq₂ {d : ℕ} {x y : fin d → ℝ} (hmaj : majorizes x y) : 
  ∑ i : fin d, | x i - y i | = ∑ i : fin (d - 1), 
  (| x (fin.cast_le (nat.sub_le d 1) i) - y (fin.cast_le (nat.sub_le d 1) i) | 
    + x (fin.cast_le (nat.sub_le d 1) i) - y (fin.cast_le (nat.sub_le d 1) i)) :=
begin
  sorry,
end

lemma compare_terms {d : ℕ} {j : fin d} {x y : fin d → ℝ} (hmaj : majorizes x y) (hj : ↑j < d) :
  | x j - y j | + x j - y j  ≤ 2 * ∑ i : fin j, (x (fin.cast_le hj i) - y (fin.cast_le hj i)) :=
begin
  sorry,
end

lemma sum_abs_le_T {d : ℕ} {x y : fin d → ℝ} (hmaj : majorizes x y) :
  ∑ i : fin d, | x i - y i | ≤ 2 * T x y :=
begin
  rw eq₁ hmaj,
  rw eq₂ hmaj,
  rw finset.mul_sum,
  apply finset.sum_le_sum,
  intro i,
  sorry
end