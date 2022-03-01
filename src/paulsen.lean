import data.matrix.basic
import data.real.basic
import analysis.normed_space.basic

open_locale big_operators

variables {n : ℕ} {d : ℕ}

def outer (v : fin d → ℝ) (u : fin d → ℝ) : matrix (fin d) (fin d) ℝ :=
λ i j, (v i) * (u j)

def outers (U : matrix (fin d) (fin n) ℝ) : matrix (fin d) (fin d) ℝ :=
  ∑ i : fin n, outer (λ j, U j i) (λ j, U j i)

def is_positive (U : matrix (fin d) (fin d) ℝ) : Prop := 

instance : partial_order (matrix (fin d) (fin d) ℝ) :=
{
  le := sorry,
  lt := sorry,
  le_refl := sorry,
  le_trans := sorry,
  lt_iff_le_not_le := sorry,
  le_antisymm := sorry
}

def is_parseval_frame (U : matrix (fin d) (fin n) ℝ) : Prop := (outers U = 1) ∧ (∀ j : (fin n), ∥ (λ i, U i j) ∥^2 = d / n)

def is_eps_parseval_frame (U : matrix (fin d) (fin n) ℝ) (ε : ℝ) : Prop := 
  ((1 + ε) • 1 ≥ outers U ∧ outers U ≥ (1 - ε) • 1) ∧ (∀ j, (1 - ε) * d / n ≤ ∥ (λ i, U i j) ∥^2 ∧ ∥ (λ i, U i j) ∥^2 ≤ (1 + ε) * d / n)


/-- Finds a nearby Parseval Frame as given in the proof, Paulsen made simple: -/

def nearby_parseval_frame {ε : ℝ} (U : matrix (fin d) (fin n) ℝ) 
  (hU : is_eps_parseval_frame U ε) : matrix (fin d) (fin n) ℝ := sorry

theorem nearby_parseval_frame_is_parseval {ε : ℝ} (U : matrix (fin d) (fin n) ℝ) 
  (hU : is_eps_parseval_frame U ε) : is_parseval_frame (nearby_parseval_frame U hU) :=
begin
  sorry
end

variables [semi_normed_group (matrix (fin d) (fin n) ℝ)] [normed_space ℝ (matrix (fin d) (fin n) ℝ)]

theorem nearby_parseval_frame_apply_is_nearby {ε : ℝ} (U : matrix (fin d) (fin n) ℝ) 
  (hU : is_eps_parseval_frame U ε) : 
    ∥ U - nearby_parseval_frame U hU ∥^2 ≤ 20 * ε * d :=
begin
  sorry
end