import data.real.basic
import algebra.big_operators.ring
import summation

variables {d n : ℕ}

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
  ∑ j : fin d, j.val • (x j - y j)

-- T x y = ∑ (j < d), ∑ (i < j) (x i - y i)
lemma T_apply {x y : fin d → ℝ} (hmaj : majorizes x y) : 
  T x y = ∑ j : fin d, (∑ i : fin (j.val), (x (fin.cast_le j.is_lt i) - y (fin.cast_le j.is_lt i))) :=
begin
  rw T,
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