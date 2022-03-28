import data.real.basic
import linear_algebra.basic
import linear_algebra.linear_independent
import analysis.normed_space.basic
import analysis.inner_product_space.euclidean_dist
import data.mv_polynomial.basic
import data.polynomial.basic
import poly_questions

open_locale big_operators classical

/-- 
The purpose of this document is to show:
  - For any set of `d` vectors `uᵢ : (fin d) → ℝ`, there exist `d` perturbations `ηᵢ : (fin d) → ℝ`
  such that the set of vectors `uᵢ + ηᵢ` are linearly independent.
  - For any set of `n` vectors `uᵢ : (fin d) → ℝ`, there exist `n` perturbations `ηᵢ : (fin d) → ℝ`
  such that any size `d` subset of `uᵢ + η_i` are linearly independent.
  - These perturbations can be made arbitrarily small.
-/

variables {M : Type*} {d n : ℕ} [add_comm_group M] [module ℝ M]
variables [has_norm M]

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

lemma matrix_dense_iff_uncurry_dense (n : ℕ) (f : ((fin n) → (fin n) → ℝ) → ℝ) : 
  dense {M : matrix (fin n) (fin n) ℝ | f M ≠ 0} ↔ dense {σ : fin n × fin n → ℝ | f (function.curry σ) ≠ 0} :=
begin
  iterate {rw dense,},
  split,
  intros h x,
  specialize h ((function.curry x) : matrix (fin n) (fin n) ℝ),
  rw metric.mem_closure_iff,
  rw metric.mem_closure_iff at h,

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

-- Warm up? (Not necessary)
def perturbations' (ε : ℝ) (u : (fin d) → (fin d) → ℝ) : fin d → fin d → ℝ :=
begin


end

lemma perturbations'_apply (ε : ℝ) (u : (fin d) → (fin d) → ℝ) : linear_independent ℝ (λ i : fin d, u i + perturbations' ε u i) := sorry

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
