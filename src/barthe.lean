import data.real.basic
import data.matrix.basic
import linear_algebra.basic
import linear_algebra.linear_independent
import linear_algebra.matrix.to_lin


variables {n d : ℕ} (U : matrix (fin d) (fin n) ℝ)

open_locale big_operators matrix

def outer (v : fin d → ℝ) (u : fin d → ℝ) : matrix (fin d) (fin d) ℝ :=
λ i j, (v i) * (u j)

def outers (U : matrix (fin d) (fin n) ℝ) : matrix (fin d) (fin d) ℝ :=
  ∑ i : fin n, outer (λ j, U j i) (λ j, U j i)

def norm_columns (U : matrix (fin d) (fin n) ℝ) : matrix (fin d) (fin n) ℝ := sorry


def radial_isotropic (U : matrix (fin d) (fin n) ℝ) 
  (hU : ∀ f : (fin d) → (fin n), linear_independent ℝ (λ i : fin d, λ j : fin d, U j (f i))) : (fin d → ℝ) →ₗ[ℝ] (fin d → ℝ) :=
  begin
    sorry
  end

theorem radial_isotropic_apply (U : matrix (fin d) (fin n) ℝ) 
  (hU : ∀ f : (fin d) → (fin n), linear_independent ℝ (λ i : fin d, λ j : fin d, U j (f i))) : 
    outers ((radial_isotropic U hU).to_matrix' ⬝ U) = (n / d  : ℝ) • 1 :=
begin
  sorry
end