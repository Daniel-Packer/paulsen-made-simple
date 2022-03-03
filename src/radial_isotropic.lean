import data.real.basic
import data.matrix.basic
import linear_algebra.basic
import linear_algebra.linear_independent
import linear_algebra.matrix.to_lin
import linear_algebra.unitary_group
import analysis.normed_space.basic

variables {n d : ℕ} (U : matrix (fin d) (fin n) ℝ)

open_locale big_operators matrix

def outer (v : fin d → ℝ) (u : fin d → ℝ) : matrix (fin d) (fin d) ℝ :=
λ i j, (v i) * (u j)

def outers (U : matrix (fin d) (fin n) ℝ) : matrix (fin d) (fin d) ℝ :=
  ∑ i : fin n, outer (Uᵀ i) (Uᵀ i)

@[simp]
lemma outer_smul_outer (v : fin d → ℝ) (u : fin d → ℝ) (c : ℝ) : outer (c • u) v = c • outer u v := sorry

@[simp]
lemma outer_outer_smul (v : fin d → ℝ) (u : fin d → ℝ) (c : ℝ) : outer u (c • v) = c • outer u v := sorry

@[simp]
lemma outers_smul (U : matrix (fin d) (fin n) ℝ) (c : ℝ) : outers (c • U) = c^2 • outers U := sorry

def norm_columns (U : matrix (fin d) (fin n) ℝ) : matrix (fin d) (fin n) ℝ := sorry

lemma norm_columns_apply_sq (U : matrix (fin d) (fin n) ℝ) : ∀ j : (fin n), ∥ (norm_columns U)ᵀ j ∥^2 = 1  := sorry

lemma norm_columns_apply (U : matrix (fin d) (fin n) ℝ) : ∀ j : (fin n), ∥ (norm_columns U)ᵀ j ∥ = 1  := sorry

def radial_isotropic (U : matrix (fin d) (fin n) ℝ) : Prop := outers (norm_columns U) = (n / d  : ℝ) • 1

lemma orthogonal_radial_isotropic_radial_isotropic (U : matrix (fin d) (fin n) ℝ)
  (O : matrix (fin d) (fin d) ℝ) (hO : O ∈ @matrix.orthogonal_group (fin d) _ _ ℝ _) :
  radial_isotropic (O ⬝ U) :=
begin
  sorry,
end

def make_radial_isotropic (U : matrix (fin d) (fin n) ℝ) 
  (hU : ∀ f : (fin d) → (fin n), function.injective f →
  linear_independent ℝ (λ i : fin d, Uᵀ (f i))) : 
    matrix (fin d) (fin d) ℝ :=
begin
  sorry
end

theorem make_radial_isotropic_apply (U : matrix (fin d) (fin n) ℝ) 
  (hU : ∀ f : (fin d) → (fin n), function.injective f →
  linear_independent ℝ (λ i : fin d, Uᵀ (f i))) : 
    radial_isotropic (make_radial_isotropic U hU ⬝ U) :=
begin
  sorry
end



