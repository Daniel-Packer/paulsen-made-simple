import data.real.basic
import order.locally_finite
import data.fin.basic
import algebra.big_operators.ring
import data.nat.interval
import algebra.big_operators.intervals
import group_theory.group_action.basic

variables (d : ℕ) (x y : ℕ → ℝ)

open_locale big_operators

-- finset.range j = finset.Ico 0 j = [0,j)

def majorizes_le : Prop :=
  ∀ j < d, ∑ (i : ℕ) in finset.Ico 1 (j.succ), y i ≤ ∑ (i : ℕ) in finset.Ico 1 (j.succ), x i

def majorizes_eq : Prop :=
  ∑ (i : ℕ) in finset.Ico 1 (d.succ), y i = ∑ (i : ℕ) in finset.Ico 1 (d.succ), x i

def T := ∑ (j : ℕ) in finset.Ico 1 (d.succ), j • (y j - x j)

lemma T_one (x y : ℕ → ℝ) (h_maj : majorizes_eq d x y) :
  T d x y = ∑ (i : ℕ) in finset.Ico 1 (d.succ), ∑ (j : ℕ) in finset.Ico 1 i, (x j - y j) :=
begin
  rw T,
  have : ∀ (j : ℕ), j • (y j - x j) = ∑ (i : ℕ) in finset.Ico 1 (j.succ), (y j - x j) :=
  λ (j : ℕ), by simp only [tsub_zero, finset.sum_sub_distrib, nat.succ_sub_succ_eq_sub,
    finset.sum_const, nsmul_eq_mul, nat.card_Ico],
  simp only [this],
  clear this,
  have : ∑ (j : ℕ) in finset.Ico 1 (d.succ), ∑ (i : ℕ) in finset.Ico 1 (j.succ), (y j - x j)
    = ∑ (i : ℕ) in finset.Ico 1 (d.succ), ∑ (j : ℕ) in finset.Ico i (d.succ), (y j - x j),
  rw finset.sum_Ico_Ico_comm,
  rw this,
  clear this,
  apply finset.sum_congr,
  simp only [eq_self_iff_true],
  intros i hi,
  rw finset.mem_Ico at hi,
  simp only [finset.sum_sub_distrib],
  rw [sub_eq_iff_eq_add, add_comm, ← add_sub_assoc],
  symmetry,
  rw sub_eq_iff_eq_add,
  rw add_comm,
  rw finset.sum_Ico_consecutive _ hi.1 (le_of_lt hi.2),
  rw add_comm,
  rw finset.sum_Ico_consecutive _ hi.1 (le_of_lt hi.2),
  rw majorizes_eq at h_maj,
  symmetry,
  exact h_maj,
end

lemma T_two (x y : ℕ → ℝ) (h_maj : majorizes_eq d x y) :
  T d x y = ∑ (i : ℕ) in finset.Ico 1 (d.succ), ∑ (j : ℕ) in finset.Ico 1 i.succ, (x j - y j) :=
begin
  rw T_one d x y h_maj,
  have : ∑ (i : ℕ) in finset.Ico 1 d.succ, ∑ (j : ℕ) in finset.Ico 1 i.succ, (x j - y j) = 
    ∑ (i : ℕ) in finset.Ico 1 d.succ, (∑ (j : ℕ) in finset.Ico 1 i, (x j - y j) + (x i - y i)) :=
  begin
    apply finset.sum_congr,
    simp only [eq_self_iff_true],
    intros i hi,
    rw finset.mem_Ico at hi,
    rw finset.sum_Ico_succ_top hi.1,
  end,
  rw this,
  rw finset.sum_add_distrib,
  simp only [finset.sum_sub_distrib, self_eq_add_right, finset.sum_congr],
  rw majorizes_eq at h_maj,
  rw h_maj,
  simp only [eq_self_iff_true, sub_self],
end

lemma T_three (x y : ℕ → ℝ) (h_d : 1 ≤ d) (h_maj : majorizes_eq d x y) :
  T d x y = ∑ (i : ℕ) in finset.Ico 1 d, ∑ (j : ℕ) in finset.Ico 1 i.succ, (x j - y j) :=
begin
  rw T_two d x y h_maj,
  rw finset.sum_Ico_succ_top h_d,
  simp only [add_right_eq_self, finset.sum_sub_distrib, finset.sum_congr],
  rw majorizes_eq at h_maj,
  rw h_maj,
  simp only [eq_self_iff_true, sub_self],
end

lemma T_four (x y : ℕ → ℝ) (h_d : 1 ≤ d) (h_maj : majorizes_eq d x y) :
  2 • (T d x y) = ∑ (i : ℕ) in finset.Ico 1 d, 2 • ∑ (j : ℕ) in finset.Ico 1 i.succ, (x j - y j) :=
begin
  rw T_three _ _ _ h_d h_maj,
  rw finset.smul_sum,
end

lemma norm_one (x y : ℕ → ℝ) (h_d : 1 ≤ d) :
  ∑ (j : ℕ) in finset.Ico 1 d.succ, |x j - y j| = ∑ (j : ℕ) in finset.Ico 1 d, |x j - y j| + | x d - y d| :=
begin
  rw finset.sum_Ico_succ_top h_d,
end

lemma norm_two (x y : ℕ → ℝ) (h_d : 1 ≤ d) (h_maj : majorizes_eq d x y) (h_majle : majorizes_le d x y):
  |x d - y d| = ∑ (j : ℕ) in finset.Ico 1 d, (x j - y j) :=
begin
  have : ∑ (j : ℕ) in finset.Ico 1 d.succ, (x j - y j) = 0 :=
  begin
    rw majorizes_eq at h_maj,
    rw finset.sum_sub_distrib,
    rw h_maj,
    simp only [eq_self_iff_true, sub_self],
  end,
  have : x d - y d = ∑ (j : ℕ) in finset.Ico 1 d, (y j - x j) :=
  begin
    rw finset.sum_Ico_succ_top at this,
    rw add_eq_zero_iff_neg_eq at this,
    rw ← this,
    norm_num,
    exact h_d,
  end,
  rw this,
  have : ∑ (j : ℕ) in finset.Ico 1 d, (x j - y j) = - ∑ (j : ℕ) in finset.Ico 1 d, (y j - x j) :=
  begin
    simp only [finset.sum_sub_distrib, eq_self_iff_true, neg_sub, sub_left_inj],
  end,
  rw this,
  rw abs_eq_neg_self,
  rw majorizes_le at h_majle,
  specialize h_majle (d - 1),
  simp only [finset.sum_sub_distrib, sub_nonpos],
  simp at h_majle,
  apply h_majle,
  linarith,
end

lemma norm_three (x y : ℕ → ℝ) (h_d : 1 ≤ d) (h_maj : majorizes_eq d x y) (h_majle : majorizes_le d x y) :
  ∑ (j : ℕ) in finset.Ico 1 d.succ, |x j - y j| = ∑ (j : ℕ) in finset.Ico 1 d, (|x j - y j| + (x j - y j)) :=
begin
  rw norm_one _ _ _ h_d,
  rw norm_two _ _ _ h_d h_maj h_majle,
  rw finset.sum_add_distrib,
end

lemma norm_le_2T (x y : ℕ → ℝ) (h_d : 1 ≤ d) (h_majle : majorizes_le d x y) (h_maj : majorizes_eq d x y):
  ∑ (j : ℕ) in finset.Ico 1 d, (|x j - y j| + (x j - y j)) ≤ 2 • (T d x y) :=
begin
  rw T_four d x y h_d h_maj,
  apply finset.sum_le_sum,
  intros i hi,
  by_cases (0 ≤ x i - y i),
  have : |x i - y i| = x i - y i :=
  begin
    rw abs_eq_self,
    exact h,
  end,
  rw this,
  clear this,
  rw finset.sum_Ico_succ_top,
  simp only [finset.sum_sub_distrib, nat.cast_bit0, nsmul_eq_mul, nat.cast_one],
  rw left_distrib,
  have : x i - y i + (x i - y i) = 2 * (x i - y i),
  ring,
  rw this,
  apply le_add_of_nonneg_left,
  rw finset.mem_Ico at hi,
  rw majorizes_le at h_majle,
  specialize h_majle (i - 1),
  rw zero_le_mul_left,
  simp only [sub_nonneg],
  have : i - 1 < d,
  linarith,
  apply h_majle this,
  norm_num,
  rw finset.mem_Ico at hi,
  exact hi.1,
  have : |x i - y i| = -(x i - y i) :=
  begin
    rw abs_eq_neg_self,
    simp only [sub_nonpos],
    simp at h,
    exact le_of_lt h,
  end,
  rw this,
  simp only [finset.sum_sub_distrib, sub_nonneg, nat.cast_bit0, zero_le_mul_left, nsmul_eq_mul,
    neg_sub, nat.cast_one, sub_add_sub_cancel', sub_self],
  rw majorizes_le at h_majle,
  specialize h_majle i,
  rw zero_le_mul_left,
  rw sub_nonneg,
  rw finset.mem_Ico at hi,
  apply h_majle hi.2,
  linarith,
end