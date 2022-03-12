import data.real.basic
import data.matrix.basic
import algebra.big_operators.basic

open_locale big_operators matrix



variables {d n : ℕ} {ι : Type*}

variables (M : matrix (fin n) (fin n) ℝ)

variables {f : fin n → ℝ} {g : fin n.succ → ℝ}

def n_set : finset (fin n) := @finset.univ (fin n) (fin.fintype n)


theorem blah : ∑ i : (fin n), ∑ j : (fin n), M i j = ∑ j : (fin n), ∑ i : (fin n), M i j :=
  finset.sum_comm


theorem sum_split_singleton (k : fin n) :
  ∑ (i : fin n), f i = f k + ∑ (i : fin n) in finset.univ \ {k}, f i :=
  finset.sum_eq_add_sum_diff_singleton (finset.mem_univ k) f

-- theorem sum_split_singleton (k : fin n) : ∑ (i : fin n), f i 
--   = ∑ (i : fin n) in finset.univ.filter (λ x : fin n, x ≠ k) , f i + f k :=
-- begin
--   classical,
--   rw ← finset.sum_filter_add_sum_filter_not _ (λ x : fin n, x ≠ k),
--   simp only [add_right_inj, finset.filter_congr_decidable, finset.sum_congr],
--   simp_rw not_ne_iff,
--   rw finset.sum_filter,
--   simp only [finset.mem_univ, if_true, eq_self_iff_true, finset.sum_ite_eq'],
-- end

theorem sum_succ_eq_sum :
  ∑ (i : fin n.succ), g i = (∑ (i : fin n), g i) + g (fin.last n) :=
begin
  rw fin.sum_univ_cast_succ,
  norm_cast,
end

theorem sum_succ_eq_sum :
  ∑ (i : fin n.succ), g i = (∑ (i : fin n), g i) + g (fin.last n) :=
begin
  rw fin.sum_univ_cast_succ,
  norm_cast,
end

theorem sum_n_succ_ne_n_eq_sum_n: 
  ∑ (i : fin n.succ) in finset.univ.filter (λ x : fin n.succ, x ≠ n), g i 
  = ∑ i : fin n, g i :=
begin
  let n_set := @finset.univ (fin n) _,
  have h : n_set.map (fin.succ_above (n)).to_embedding = (@finset.univ (fin n.succ) _).filter (λ x : fin n.succ, x ≠ n) :=
  begin
    ext,
    rw finset.mem_filter,
    rw finset.mem_map,
    split,
    intro h,
    cases h with i h,
    cases h with hi h,
    split,
    exact finset.mem_univ a,
    intro c,
    rw c at h,
    simp only [nat.cast_succ, rel_embedding.coe_fn_to_embedding] at h,
    exact fin.succ_above_ne (n) i h,
    intro h,
    use (↑a),
    have := fin.is_le a,
    cases h with h1 h2,
    rw fin.ne_iff_vne at h2,
    rw fin.val_eq_coe at h2,
    rw fin.val_eq_coe at h2,
    rw fin.coe_of_nat_eq_mod at h2,
    rw nat.mod_eq_of_lt at h2,
    exact lt_of_le_of_ne this h2,
    exact nat.lt_succ_self n,
    split,
    simp only [finset.mem_univ],
    simp only [rel_embedding.coe_fn_to_embedding],
    rw fin.succ_above_below,
    simp only [eq_self_iff_true, fin.cast_succ_mk, fin.eta],
    simp only [fin.cast_succ_mk, fin.eta],
    have := fin.is_le a,
    cases h with h1 h2,
    rw fin.lt_def,
    simp only [fin.val_eq_coe, fin.coe_of_nat_eq_mod],
    rw nat.mod_eq_of_lt,
    rw fin.ne_iff_vne at h2,
    rw fin.val_eq_coe at h2,
    rw fin.val_eq_coe at h2,
    rw fin.coe_of_nat_eq_mod at h2,
    rw nat.mod_eq_of_lt at h2,
    apply lt_of_le_of_ne this _,
    exact h2,
    exact nat.lt_succ_self n,
    exact nat.lt_succ_self n,
  end,
  rw ← h,
  simp only [fin.coe_eq_cast_succ, finset.sum_map, rel_embedding.coe_fn_to_embedding, finset.sum_congr],
  congr,
  ext,
  rw fin.succ_above_below,
  have := fin.cast_succ_lt_last x,
  rw fin.lt_def at this,
  simp only [fin.val_eq_coe, fin.coe_last, fin.coe_cast_succ] at this,
  rw fin.lt_def,
  simp only [fin.val_eq_coe, fin.coe_cast_succ, fin.coe_of_nat_eq_mod],
  rw nat.mod_eq_of_lt,
  exact this,
  exact nat.lt_succ_self n,
end


theorem sum_split_last (f : fin n.succ → ℝ) : ∑ (i : fin n.succ), f i 
  = ∑ (i : fin n), f i + f n :=
begin
  rw sum_split_singleton (n : fin n.succ),
  rw sum_n_succ_ne_n_eq_sum_n,
end

theorem sum_nonneg_of_nonneg (h : ∀ i : fin n, 0 ≤ f i) : 0 ≤ ∑ i : fin n, f i :=
begin
  have : ∀ (i : fin n), i ∈ @finset.univ (fin n) _ → 0 ≤ f i :=
  begin
    intros i hi,
    exact h i,
  end,
  exact finset.sum_nonneg this,
end

-- theorem sum_nonneg_of_nonneg (h : ∀ i : fin n, 0 ≤ f i) : 0 ≤ ∑ i : fin n, f i :=
-- begin
--   induction n with n h0,
--   simp only [le_refl, finset.sum_empty, finset.sum_congr, fintype.univ_of_is_empty],
--   rw sum_split_singleton (n : fin n.succ),
--   rw sum_n_succ_ne_n_eq_sum_n,
--   let g := f ∘ fin.succ_above n,
--   have : ∀ i : fin n, 0 ≤ g i :=
--   begin
--     intro i,
--     change 0 ≤ (f ∘ fin.succ_above n) i,
--     rw function.comp_app,
--     exact h _,
--   end,
--   have hg: ∀ i : fin n, g i = f i := λ i,
--   begin
--     simp only [g],
--     rw function.comp_app,
--     rw fin.succ_above_below,
--     rw fin.coe_eq_cast_succ,
--     rw [fin.lt_def, fin.val_eq_coe, fin.val_eq_coe, fin.coe_cast_succ, fin.coe_of_nat_eq_mod],
--     rw nat.mod_eq_of_lt (nat.lt_succ_self n),
--     apply fin.cast_succ_lt_last,
--   end,
--   simp_rw ← hg,
--   apply add_nonneg,
--   exact h0 this,
--   exact h n,
-- end

#check (fintype(fin n))
#check @finset.univ (fin n) (fin.fintype n) -- : finset (fin n)