import data.real.basic
import data.matrix.basic
import algebra.big_operators.basic

open_locale big_operators matrix



variables {d n : ℕ} {ι : Type*}

variables (M : matrix (fin n) (fin n) ℝ)

variable {f : fin n → ℝ}

def n_set : finset (fin n) := @finset.univ (fin n) (fin.fintype n)


theorem blah : ∑ i : (fin n), ∑ j : (fin n), M i j = ∑ j : (fin n), ∑ i : (fin n), M i j := finset.sum_comm

theorem sum_nonneg_of_nonneg (h : ∀ i : fin n, 0 ≤ f i) : 0 ≤ ∑ i : fin n, f i :=
begin
  induction n with n h0,
  simp only [le_refl, finset.sum_empty, finset.sum_congr, fintype.univ_of_is_empty],

end

theorem sum_split_singleton (k : fin n) : ∑ (i : fin n), f i 
  = ∑ (i : fin n) in finset.filter (λ x : fin n, x ≠ k) (@finset.univ (fin n) (fin.fintype n)), f i + f k :=
begin
  classical,
  rw ← finset.sum_filter_add_sum_filter_not _ (λ x : fin n, x ≠ k),
  simp only [add_right_inj, finset.filter_congr_decidable, finset.sum_congr],
  simp_rw not_ne_iff,
  rw finset.sum_filter,
  simp only [finset.mem_univ, if_true, eq_self_iff_true, finset.sum_ite_eq'],
end

#check (fintype(fin n))
#check @finset.univ (fin n) (fin.fintype n) -- : finset (fin n)