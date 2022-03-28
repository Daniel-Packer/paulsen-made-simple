import data.real.basic
import linear_algebra.basic
import linear_algebra.linear_independent
import analysis.normed_space.basic
import analysis.inner_product_space.euclidean_dist
import data.mv_polynomial.basic
import data.polynomial.basic
import poly_questions
import topology.category.Profinite.default
import data.matrix.basic
import linear_algebra.matrix.to_linear_equiv

open_locale big_operators classical matrix

/-- 
The purpose of this document is to show:
  - For any set of `d` vectors `uᵢ : (fin d) → ℝ`, there exist `d` perturbations `ηᵢ : (fin d) → ℝ`
  such that the set of vectors `uᵢ + ηᵢ` are linearly independent.
  - For any set of `n` vectors `uᵢ : (fin d) → ℝ`, there exist `n` perturbations `ηᵢ : (fin d) → ℝ`
  such that any size `d` subset of `uᵢ + η_i` are linearly independent.
  - These perturbations can be made arbitrarily small.
-/
variables {n : ℕ}

def perm_graph (perm : equiv.perm (fin n)) : (fin n × fin n) → ℕ := λ ⟨i, j⟩, if perm j = i then 1 else 0

noncomputable def perm_graph' (perm : equiv.perm (fin n)) : (fin n × fin n) →₀ ℕ := ∑ i : fin n, finsupp.single (perm i, i) 1

lemma perm_graph'_apply (perm : equiv.perm (fin n)) (ij : fin n × fin n) : perm_graph' perm ij = 
if perm (ij.snd) = ij.fst then 1 else 0 :=
begin
  rw perm_graph',
  by_cases hij : perm ij.snd = ij.fst,
  have : ∀ x : fin n, (perm x, x) = ij ↔ x = ij.snd :=
  begin
    intro x,
    split,
    intro h,
    rw ← h,
    intro h,
    rw h,
    rw hij,
    rw prod.mk.eta,
  end,
  simp only [if_true, eq_self_iff_true, hij],
  rw finsupp.finset_sum_apply,
  simp_rw finsupp.single_apply,
  simp_rw this,
  rw finset.sum_ite_eq',
  simp only [finset.mem_univ, if_true, eq_self_iff_true],
  simp only [hij, if_false],
  rw finsupp.finset_sum_apply,
  simp_rw finsupp.single_apply,
  have : ∀ x : fin n, (perm x, x) ≠ ij :=
  begin
    intros x heq,
    rw prod.ext_iff at heq,
    by_cases h : x = ij.snd,
    rw h at heq,
    simp only [and_true, eq_self_iff_true] at heq,
    exact hij heq,
    simp only [] at heq,
    exact h heq.2,
  end,
  simp only [this, eq_self_iff_true, if_false, finset.sum_const_zero, finset.sum_congr],
end

def perm_graph_supp (perm : equiv.perm (fin n)) : set (fin n × fin n) := {ij | perm (ij.snd) = ij.fst}

noncomputable def perm_monomial {n : ℕ} (perm : equiv.perm (fin n)) : mv_polynomial (fin n × fin n) ℝ :=
mv_polynomial.monomial (perm_graph' perm) 1

noncomputable def det_as_poly' (n : ℕ) : mv_polynomial (fin n × fin n) ℝ :=
∑ p : equiv.perm (fin n), (p.sign : ℝ) • perm_monomial p


lemma det_as_poly_eq_det' (n : ℕ) (M : matrix (fin n) (fin n) ℝ) : mv_polynomial.eval (function.uncurry M) (det_as_poly' n) = M.det :=
begin
  rw det_as_poly',
  rw mv_polynomial.eval_sum,
  simp_rw [mv_polynomial.smul_eval, perm_monomial, mv_polynomial.eval_monomial],
  simp only [one_mul, finsupp.prod_pow, finset.sum_congr, coe_coe, perm_graph'_apply],
  simp only [finset.prod_congr, pow_boole, finset.sum_congr],
  rw matrix.det_apply,
  congr' 1,
  ext p,
  rw ← finset.univ_product_univ,
  simp_rw function.uncurry,
  let f : fin n → fin n → ℝ := λ i j, ite (p j = i) (M i j) 1,
  have : ∀ i j : fin n, f i j = ite (p j = i) (M i j) 1 := λ i j, rfl,
  simp_rw ← this,
  rw @finset.prod_product_right' ℝ (fin n) (fin n) _ finset.univ finset.univ _,
  simp only [f],
  have foo : ∀ (b : ℝ), p.sign • b = (p.sign : ℝ) * b :=
  begin
    intros,
    simp only [coe_coe],
    rw ← zsmul_eq_mul,
    congr,
  end,
  rw [foo, coe_coe],
  congr' 2,
  ext,
  rw finset.prod_ite_eq,
  simp only [finset.mem_univ, if_true, eq_self_iff_true],
end

-- instance : topological_space (fin n) := ⊥
-- instance : discrete_topology (fin n) := ⟨ rfl ⟩

-- noncomputable instance foo : semi_normed_group (matrix (fin n) (fin n) ℝ) := matrix.semi_normed_group
noncomputable instance foo2 : normed_group (matrix (fin n) (fin n) ℝ) := matrix.normed_group


def matrix_homeomorph_prod_fun (n : ℕ) : matrix (fin n) (fin n) ℝ ≃ₜ (fin n × fin n → ℝ) :=
{
  to_equiv :={
  to_fun := function.uncurry,
  inv_fun := function.curry,
  left_inv := λ x, by {rw function.curry_uncurry},
  right_inv := λ x, by {rw function.uncurry_curry},
  },
  continuous_to_fun := 
  begin
    simp only [],
    rw metric.continuous_iff,
    intros,
    use ε,
    split,
    exact H,
    intros a ha,
    rw dist_eq_norm,
    simp only [norm],
    rw dist_eq_norm at ha,
    simp_rw [pi.sub_apply, function.uncurry_def],
    rw ← real.coe_to_nnreal ε (le_of_lt H),
    rw nnreal.coe_lt_coe,
    rw finset.sup_lt_iff,
    intros ij _,
    rw pi_norm_lt_iff H at ha,
    specialize ha ij.fst,
    rw pi.sub_apply at ha,
    rw pi_norm_lt_iff H at ha,
    specialize ha ij.snd,
    rw real.norm_eq_abs at ha,
    rw ← nnreal.coe_lt_coe,
    simp only [real.coe_to_nnreal', lt_max_iff, coe_nnnorm, real.norm_eq_abs],
    left,
    exact ha,
    rw ← nnreal.coe_lt_coe,
    simp only [lt_self_iff_false, real.coe_to_nnreal', nonneg.coe_zero, lt_max_iff, bot_eq_zero, or_false],
    exact H,
  end,
  continuous_inv_fun := 
  begin
    simp only [],
    rw metric.continuous_iff,
    intros,
    use ε,
    split,
    exact H,
    intros a ha,
    rw dist_eq_norm,
    rw dist_eq_norm at ha,
    simp only [norm] at ha,
    simp_rw [pi.sub_apply] at ha,
    rw pi_norm_lt_iff H,
    intro i,
    rw pi_norm_lt_iff H,
    intro j,
    simp_rw [pi.sub_apply],
    rw real.norm_eq_abs,
    rw ← real.coe_to_nnreal ε (le_of_lt H) at ha,
    rw nnreal.coe_lt_coe at ha,
    rw finset.sup_lt_iff at ha,
    specialize ha (i, j),
    simp_rw function.curry_apply,
    simp_rw ← nnreal.coe_lt_coe at ha,
    simp only [lt_self_iff_false, real.coe_to_nnreal', nonneg.coe_zero, lt_max_iff, bot_eq_zero, or_false, coe_nnnorm, real.norm_eq_abs, abs_nonneg] at ha,
    specialize ha (finset.mem_univ _),
    have : ¬ |a (i, j) - b (i, j) | < 0 := by {simp only [not_lt], exact abs_nonneg _},
    simp only [this, or_false] at ha,
    exact ha,
    simp only [real.to_nnreal_pos, bot_eq_zero],
    exact H,
  end,
}

lemma matrix_homeomorph_prod_fun.symm_apply {n : ℕ} (σ : (fin n) × (fin n) → ℝ) : (matrix_homeomorph_prod_fun n).symm σ = function.curry σ := rfl
lemma matrix_homeomorph_prod_fun.apply {n : ℕ} (m : matrix (fin n) (fin n) ℝ) : (matrix_homeomorph_prod_fun n) m = function.uncurry m := rfl

lemma matrix_curry_map_nonzero (n : ℕ)
  (f : (fin n → fin n → ℝ) → ℝ) :
  {σ : fin n × fin n → ℝ | f (function.curry σ) ≠ 0} =
    ⇑(matrix_homeomorph_prod_fun n) ''
      {m : matrix (fin n) (fin n) ℝ | f m ≠ 0} :=
begin
  rw set.image,
  ext,
  iterate{rw set.mem_set_of_eq,},
  split,
  intro h,
  use (matrix_homeomorph_prod_fun n).symm x,
  rw set.mem_set_of_eq,
  simp only [homeomorph.apply_symm_apply, and_true, eq_self_iff_true],
  rw matrix_homeomorph_prod_fun.symm_apply,
  exact h,
  intro h,
  choose a ha using h,
  rw ← ha.2,
  rw set.mem_set_of_eq at ha,
  rw matrix_homeomorph_prod_fun.apply,
  simp only [function.curry_uncurry],
  exact ha.1,
end

lemma matrix_dense_iff_uncurry_dense (n : ℕ) (f : ((fin n) → (fin n) → ℝ) → ℝ) : 
  dense {m : matrix (fin n) (fin n) ℝ | f m ≠ 0} ↔ dense {σ : fin n × fin n → ℝ | f (function.curry σ) ≠ 0} :=
begin
  -- simp [(matrix_homeomorph_prod_fun n)],
  iterate {rw dense,},
  rw matrix_curry_map_nonzero n,
  rw ← homeomorph.image_closure (matrix_homeomorph_prod_fun n) _,
  simp_rw set.mem_image,
  split,
  intro h,
  intro x,
  use (matrix_homeomorph_prod_fun n).symm x,
  specialize h ((matrix_homeomorph_prod_fun n).symm x),
  simp only [homeomorph.apply_symm_apply, and_true, eq_self_iff_true],
  exact h,
  intros h x,
  specialize h (matrix_homeomorph_prod_fun n x),
  choose y hy using h,
  rw (matrix_homeomorph_prod_fun n).injective.eq_iff at hy,
  rw ← hy.2,
  exact hy.1,
end

lemma nonzero_det_dense (n : ℕ) : dense {M : matrix (fin n) (fin n) ℝ | M.det ≠ 0} :=
begin
  simp_rw [← det_as_poly_eq_det' n _],
  rw matrix_dense_iff_uncurry_dense,
  simp_rw function.uncurry_curry,
  apply mvpoly_nonzero_dense,
  intro h,
  rw mv_polynomial.funext_iff at h,
  specialize h (function.uncurry (1 : matrix (fin n) (fin n) ℝ)),
  rw [det_as_poly_eq_det', map_zero, matrix.det_one] at h,
  exact one_ne_zero h,
end

lemma det_ne_zero_iff_cols_linear_independent {n : ℕ} (M : matrix (fin n) (fin n) ℝ) : 
  M.det ≠ 0 ↔ linear_independent ℝ (λ i : fin n, M i) :=
begin
  rw ← matrix.nondegenerate_iff_det_ne_zero,
  rw fintype.linear_independent_iff,
  split,
  intro h,
  intros g hg,
  have : (∀ (w : fin n → ℝ), g ⬝ᵥ M.mul_vec w = 0) → g = 0 := matrix.nondegenerate.eq_zero_of_ortho h,
  suffices H : g = 0,
  rw H,
  simp only [pi.zero_apply, eq_self_iff_true, implies_true_iff],
  apply this,
  intro w,
  rw matrix.dot_product_mul_vec,
  have : matrix.vec_mul g M = 0 :=
  begin
    ext,
    simp only [pi.zero_apply],
    rw matrix.vec_mul,
    rw matrix.dot_product,
    rw function.funext_iff at hg,
    specialize hg x,
    simp only [algebra.id.smul_eq_mul,
 matrix.transpose_apply,
 pi.zero_apply,
 fintype.sum_apply,
 pi.smul_apply,
 finset.sum_congr] at hg,
 exact hg,
  end,
  rw this,
  simp only [eq_self_iff_true, matrix.zero_dot_product],
  intro H,
  intro v,
  specialize H v,
  intro hv,
  rw function.funext_iff,
  apply H,
  rw function.funext_iff,
  intro a,
  simp only [algebra.id.smul_eq_mul, pi.zero_apply, fintype.sum_apply, pi.smul_apply, finset.sum_congr],
  specialize hv (pi.single a 1),
  rw matrix.dot_product_mul_vec at hv,
  rw matrix.dot_product at hv,
  have : ∀ i : fin n, matrix.vec_mul v M i * pi.single a 1 i = pi.single a (matrix.vec_mul v M a) i :=
  begin
    intro i,
    by_cases hi : a = i,
    rw hi,
    simp only [mul_one, eq_self_iff_true, pi.single_eq_same],
    iterate{rw pi.single_eq_of_ne' hi,},
    rw mul_zero,
  end,
  simp_rw this at hv,
  rw finset.sum_pi_single' a (matrix.vec_mul v M a) _ at hv,
  simp only [finset.mem_univ, if_true] at hv,
  simpa using hv,
end

lemma exists_nearby_matrix (M : matrix (fin n) (fin n) ℝ) (ε : ℝ) (hε : ε > 0): 
  ∃ M' : matrix (fin n) (fin n) ℝ, M'.det ≠ 0 ∧ dist M M' < ε :=
begin
  have matrix_nonzero_dense := nonzero_det_dense n,
  rw dense at matrix_nonzero_dense,
  specialize matrix_nonzero_dense M,
  rw metric.mem_closure_iff at matrix_nonzero_dense,
  specialize matrix_nonzero_dense ε hε,
  simp_rw set.mem_set_of_eq at matrix_nonzero_dense,
  simpa using matrix_nonzero_dense,
end

noncomputable def nonzero_det_matrix_nearby {n : ℕ} (M : matrix (fin n) (fin n) ℝ) (ε : ℝ) (hε : ε > 0) :
  matrix (fin n) (fin n) ℝ :=
classical.some (exists_nearby_matrix M ε hε)

lemma nonzero_det_matrix_nearby_apply {n : ℕ} (M : matrix (fin n) (fin n) ℝ) (ε : ℝ) (hε : ε > 0) :
  (nonzero_det_matrix_nearby M ε hε).det ≠ 0 :=
(classical.some_spec (exists_nearby_matrix M ε hε)).1

lemma nonzero_det_matrix_nearby_apply' {n : ℕ} (M : matrix (fin n) (fin n) ℝ) (ε : ℝ) (hε : ε > 0) :
  dist M (nonzero_det_matrix_nearby M ε hε) < ε :=
(classical.some_spec (exists_nearby_matrix M ε hε)).2

-- Warm up? (Not necessary)
noncomputable def perturbations' (ε : ℝ) (hε : ε > 0) (u : matrix (fin n) (fin n) ℝ) : matrix (fin n) (fin n) ℝ :=
nonzero_det_matrix_nearby u ε hε - u

lemma perturbations'_apply (ε : ℝ) (hε : ε > 0) (u : matrix (fin n) (fin n) ℝ) : 
  linear_independent ℝ (λ i : fin n, uᵀ i + (perturbations' ε hε u)ᵀ i) :=
begin
  rw perturbations',
  rw ← det_ne_zero_iff_cols_linear_independent,
  simpa using (nonzero_det_matrix_nearby_apply _ _ _),
end

lemma perturbations'_bound (ε : ℝ) (u : (fin d) → fin d → ℝ) : ∀ i : fin d, ∥ to_euclidean (perturbations' ε u i) ∥^2 ≤ ε := sorry

def perturbation_small (ε : ℝ) (u v : fin d → ℝ) : fin d → ℝ  := sorry

lemma perturbation_small_apply (ε : ℝ) (u v : fin d → ℝ) : 
  linear_independent ℝ (λ i : bool, if i then u + perturbation_small ε u v else v):=
begin

end

--What we actually need:
def perturbations (ε : ℝ) (u : (fin n) → fin d → ℝ) : fin n → fin d → ℝ := sorry

/-- The perturbations make -/
lemma perturbations_apply (ε : ℝ) (u : (fin n) → fin d → ℝ) {f : (fin d) → (fin n)} (hf : function.injective f) : 
  linear_independent ℝ (λ i : fin d, u (f i) + perturbations ε u (f i)) := sorry

lemma perturbations_bound (ε : ℝ) (u : (fin n) → fin d → ℝ) : ∀ i : fin n, ∥ to_euclidean (perturbations ε u i) ∥^2 ≤ ε := sorry
