import data.matrix.basic
import data.real.basic
import analysis.normed_space.basic

variables {n : ℕ} {d : ℕ}

def is_parseval_frame (U : matrix (fin d) (fin n) ℝ) : Prop := sorry
def is_eps_parseval_frame (U : matrix (fin d) (fin n) ℝ) (ε : ℝ) : Prop := sorry


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