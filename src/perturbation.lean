import data.real.basic
import linear_algebra.basic
import linear_algebra.linear_independent
import analysis.normed_space.basic

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
-- variable [finite_dimensional.finrank ℝ M = d] <- Want to include this somehow

def perturbations' (ε : ℝ) (u : (fin d) → M) : fin d → M := sorry

lemma perturbations'_apply (ε : ℝ) (u : (fin d) → M) : linear_independent ℝ (λ i : fin d, u i + perturbations' ε u i) := sorry

lemma perturbations'_bound (ε : ℝ) (u : (fin d) → M) : ∀ i : fin d, ∥ perturbations' ε u i ∥^2 ≤ ε := sorry

def perturbations (ε : ℝ) (u : (fin n) → M) : fin n → M := sorry

def d_to_n (i : fin d) : (fin n) := sorry

lemma perturbations_apply (ε : ℝ) (u : (fin n) → M) : linear_independent ℝ (λ i : fin d, u (d_to_n i) + perturbations ε u (d_to_n i)) := sorry

lemma perturbations_bound (ε : ℝ) (u : (fin n) → M) : ∀ i : fin d, ∥ perturbations ε u (d_to_n i) ∥^2 ≤ ε := sorry
