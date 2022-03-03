import data.real.basic
import linear_algebra.basic
import linear_algebra.linear_independent
import analysis.normed_space.basic


open_locale big_operators

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

-- Warm up? (Not necessary)
def perturbations' (ε : ℝ) (u : (fin d) → M) : fin d → M := sorry

lemma perturbations'_apply (ε : ℝ) (u : (fin d) → M) : linear_independent ℝ (λ i : fin d, u i + perturbations' ε u i) := sorry

lemma perturbations'_bound (ε : ℝ) (u : (fin d) → M) : ∀ i : fin d, ∥ perturbations' ε u i ∥^2 ≤ ε := sorry


--What we actually need:
def perturbations (ε : ℝ) (u : (fin n) → M) : fin n → M := sorry

/-- The perturbations make -/
lemma perturbations_apply (ε : ℝ) (u : (fin n) → M) {f : (fin d) → (fin n)} (hf : function.injective f) : 
  linear_independent ℝ (λ i : fin d, u (f i) + perturbations ε u (f i)) := sorry

lemma perturbations_bound (ε : ℝ) (u : (fin n) → M) : ∀ i : fin n, ∥ perturbations ε u i ∥^2 ≤ ε := sorry
