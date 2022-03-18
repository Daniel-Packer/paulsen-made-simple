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
  ∀ j < d, ∑ (i : ℕ) in (finset.range j), y i ≤ ∑ (i : ℕ) in (finset.range j), x i

def majorizes_eq : Prop :=
  ∑ (i : ℕ) in (finset.range d), y i = ∑ (i : ℕ) in (finset.range d), x i

def T := ∑ (j : ℕ) in (finset.range d), j • (y j - x j)

-- T(x,y) = ∑ (i < d), ∑ (j < i), (x j - y j)
-- something is weird here with using (finset.range i), since when i = 0 we still want (x 0 - y 0).
lemma T_alt_without_last (x y : ℕ → ℝ) (h_maj : majorizes_eq d x y) :
  T d x y =
  ∑ (i : ℕ) in (finset.range d), ∑ (j : ℕ) in (finset.range i), (x j - y j) :=
begin
  rw T,
  have : ∀ (j : ℕ), j • (y j - x j) = ∑ (i : ℕ) in (finset.range j), (y j - x j) := λ (j : ℕ),
    by simp only [finset.sum_sub_distrib, finset.sum_const, nsmul_eq_mul, finset.card_range],
  simp only [this],
  clear this,
  have : ∑ (j : ℕ) in finset.range d, ∑ (i : ℕ) in finset.range j, (y j - x j)
    = ∑ (i : ℕ) in finset.range d, ∑ (j : ℕ) in finset.Ico i d, (y j - x j) :=
  begin
    simp only [finset.range_eq_Ico],
    rw finset.sum_Ico_Ico_comm,
    simp only [finset.sum_Ico_succ_top (nat.zero_le _) _],
    rw finset.sum_add_distrib,
    simp only [finset.sum_sub_distrib, finset.sum_const, nsmul_eq_mul, nat.Ico_zero_eq_range,
      self_eq_add_right, finset.card_range, finset.sum_congr],
    rw majorizes_eq at h_maj,
    linarith,
  end,
  rw this,
  clear this,
  rw majorizes_eq at h_maj,
  apply finset.sum_congr,
  simp only [eq_self_iff_true],
  intro i,
  intro hi,
  simp only [finset.sum_sub_distrib],
  rw [sub_eq_iff_eq_add, add_comm],
  symmetry,
  rw [← add_sub_assoc, sub_eq_iff_eq_add, add_comm],
  nth_rewrite 1 add_comm,
  have : (finset.range i).sum x + (finset.Ico i d).sum x = (finset.range d).sum x :=
  begin
    rw finset.sum_range_add_sum_Ico,
    rw finset.mem_range at hi,
    linarith,
  end,
  rw this,
  clear this,
  have : (finset.range i).sum y + (finset.Ico i d).sum y = (finset.range d).sum y :=
  begin
    rw finset.sum_range_add_sum_Ico,
    rw finset.mem_range at hi,
    linarith,
  end,
  rw [this, h_maj],
end

lemma eq1 (x y : ℕ → ℝ) (h_maj : majorizes_eq d x y) :
  2 • (T d x y) = ∑ (i : ℕ) in (finset.range d), ∑ (j : ℕ) in (finset.range i), 2 • (x j - y j) :=
begin
  rw T_alt_without_last,
  simp only [finset.smul_sum],
  exact h_maj,
end

-- T(x,y) = ∑ (i ≤ d), ∑ (j < i), (x j - y j)
lemma T_alt_with_last (x y : ℕ → ℝ) (h_maj : majorizes_eq d x y) :
  T d x y =
  ∑ (i : ℕ) in (finset.range (d + 1)), ∑ (j : ℕ) in (finset.range i), (x j - y j) :=
begin
  have : ∑ (i : ℕ) in (finset.range (d + 1)), ∑ (j : ℕ) in (finset.range i), (x j - y j)
    = ∑ (i : ℕ) in (finset.range d), ∑ (j : ℕ) in (finset.range i), (x j - y j) +
      ∑ (j : ℕ) in (finset.range d), (x j - y j) :=
  begin
    exact finset.sum_range_succ (λ (x_1 : ℕ), ∑ (j : ℕ) in finset.range x_1, (x j - y j)) d,
  end,
  rw T_alt_without_last,
  rw this,
  simp only [finset.sum_sub_distrib, self_eq_add_right, finset.sum_congr],
  rw majorizes_eq at h_maj,
  norm_num at h_maj,
  linarith,
  exact h_maj,
end