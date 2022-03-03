import data.real.sqrt
import linear_algebra.matrix.is_diag
import radial_isotropic
import psd
import perturbation
import analysis.special_functions.pow

open_locale big_operators matrix

variables {n d: ℕ} (hnd : (n : ℝ) * (d : ℝ) ≠ (0 : ℝ))

noncomputable instance fro : has_norm (matrix (fin d) (fin n) ℝ) :=
{
  norm := λ M, real.sqrt(∑ i : fin d, ∑ j : fin n, M i j^2),
}

-- Uᵀ : fin n → fin d → ℝ
/-- U is the collection of vectors that are an almost ε parseval frame: -/
def is_parseval_frame (U : matrix (fin d) (fin n) ℝ) : Prop := 
  (outers U = 1) ∧ (∀ j : (fin n), ∥ Uᵀ j ∥^2 = d / n)

def is_eps_parseval_frame (U : matrix (fin d) (fin n) ℝ) (ε : ℝ) : Prop := 
  ((1 + ε) • 1 ≥ outers U ∧ outers U ≥ (1 - ε) • 1) ∧ (∀ j, (1 - ε) * d / n ≤ ∥ Uᵀ j ∥^2 ∧ ∥ Uᵀ j ∥^2 ≤ (1 + ε) * d / n)


/-- Finds a nearby Parseval Frame as given in the proof, Paulsen made simple: -/

noncomputable def nearby_parseval_frame {ε : ℝ} (V : matrix (fin d) (fin n) ℝ) 
  (hV : is_eps_parseval_frame V ε) : matrix (fin d) (fin n) ℝ :=
begin
  let V_norm := (real.sqrt(d / n)) • norm_columns(V),
  let η := perturbations ε V_normᵀ,
  let U := V_norm + ηᵀ,

  have h1 : ∀ i : fin n, ∥ Uᵀ i - Vᵀ i ∥^2 ≤
    (real.sqrt(d / n) - real.sqrt((1 - ε) * d / n))^2 + ∥ η i ∥^2 + 2 * ∥ η i ∥ :=
  begin
    sorry
  end,
  have h2 : ∀ i : fin n, ∥ Uᵀ i - Vᵀ i ∥^2 ≤
    ε * d / n :=
  begin
    sorry
  end,
  have h3 : is_eps_parseval_frame U (4 * ε) :=
  begin
    sorry
  end,
  have h4 : ∀ f : fin d → (fin n), function.injective f → linear_independent ℝ (λ i : fin d, Uᵀ (f i)) :=
  begin
    intros f hf,
    have hU := perturbations_apply ε V_normᵀ hf,
    suffices : (λ i : fin d, V_normᵀ (f i) + η (f i)) = λ i, Uᵀ (f i),
    rw ← this,
    exact hU,
    funext x,
    change V_normᵀ (f x) + η (f x) = (V_norm + ηᵀ)ᵀ (f x),
    rw matrix.transpose_add,
    rw matrix.transpose_transpose,
    exact (pi.add_apply (V_normᵀ) (η) (f x)).symm,
  end,

  let A := make_radial_isotropic U h4,
  have hA : radial_isotropic (A ⬝ U) := make_radial_isotropic_apply U h4,

  --need SVD to show these results (will also use orthogonal_radial_isotropic_radial_isotropic)
  let A' : matrix (fin d) (fin d) ℝ := sorry,
  have hA' : radial_isotropic (A' ⬝ U) := sorry,
  have hA'_diag : A'.is_diag := sorry,

  exact real.sqrt (d / n) • norm_columns (A' ⬝ U),
end

theorem nearby_parseval_frame_is_parseval {ε : ℝ} (hnd : (n : ℝ) * d ≠ 0) (V : matrix (fin d) (fin n) ℝ) 
  (hV : is_eps_parseval_frame V ε) : is_parseval_frame (nearby_parseval_frame V hV) :=
begin
  let V_norm := (real.sqrt(d / n)) • norm_columns(V),
  let η := perturbations ε V_normᵀ,
  let U := V_norm + ηᵀ,

  have h1 : ∀ i : fin n, ∥ Uᵀ i - Vᵀ i ∥^2 ≤
    (real.sqrt(d / n) - real.sqrt((1 - ε) * d / n))^2 + ∥ η i ∥^2 + 2 * ∥ η i ∥ :=
  begin
    sorry
  end,
  have h2 : ∀ i : fin n, ∥ Uᵀ i - Vᵀ i ∥^2 ≤
    ε * d / n :=
  begin
    sorry
  end,
  have h3 : is_eps_parseval_frame U (4 * ε) :=
  begin
    sorry
  end,
  have h4 : ∀ f : fin d → (fin n), function.injective f → linear_independent ℝ (λ i : fin d, Uᵀ (f i)) :=
  begin
    intros f hf,
    have hU := perturbations_apply ε V_normᵀ hf,
    suffices : (λ i : fin d, V_normᵀ (f i) + η (f i)) = λ i, Uᵀ (f i),
    rw ← this,
    exact hU,
    funext x,
    change V_normᵀ (f x) + η (f x) = (V_norm + ηᵀ)ᵀ (f x),
    rw matrix.transpose_add,
    rw matrix.transpose_transpose,
    exact (pi.add_apply (V_normᵀ) (η) (f x)).symm,
  end,

  let A := make_radial_isotropic U h4,
  have hA : radial_isotropic (A ⬝ U) := make_radial_isotropic_apply U h4,

  -- need SVD to show these results (will also use orthogonal_radial_isotropic_radial_isotropic)
  -- A puts U in radial isotropic position
  -- A = D Σ Eᵀ , so D Σ Eᵀ U is radial isotropic
  -- Σ U is radial isotropic
  -- Maybe reinterpet without matrices?
  let A' : matrix (fin d) (fin d) ℝ := sorry,
  have hA' : radial_isotropic (A' ⬝ U) := sorry,
  have hA'_diag : A'.is_diag := sorry,

  let W := real.sqrt (d / n) • norm_columns (A' ⬝ U),
  have def_W : ∀ i : fin n, Wᵀ i = real.sqrt (d / n) • (norm_columns (A' ⬝ U))ᵀ i := sorry,

  change is_parseval_frame W,
  rw is_parseval_frame,
  split,
  rw outers,
  rw radial_isotropic at hA',
  rw outers at hA',
  simp_rw [def_W],
  simp_rw [outer_outer_smul, outer_smul_outer],
  have nd_nonneg : 0 ≤ ((d / n) : ℝ) := sorry,
  simp_rw [smul_smul, real.mul_self_sqrt nd_nonneg],
  rw ← finset.smul_sum,
  rw hA',
  rw smul_smul,
  field_simp,
  rw mul_comm,
  rw div_self hnd,
  rw one_smul,


  intro j,
  rw def_W j,
  rw norm_smul,
  rw sq,
  rw norm_columns_apply (A' ⬝ U) j,
  rw mul_one,
  rw real.norm_eq_abs,
  rw ← abs_mul,
  rw real.mul_self_sqrt,
  rw abs_eq_self,
  apply div_nonneg,
  exact nat.cast_nonneg d,
  exact nat.cast_nonneg n,
  apply div_nonneg,
  exact nat.cast_nonneg d,
  exact nat.cast_nonneg n,

end

variables [semi_normed_group (matrix (fin d) (fin n) ℝ)] [normed_space ℝ (matrix (fin d) (fin n) ℝ)]

noncomputable def W' {ε γ' : ℝ} {U : matrix (fin d) (fin n) ℝ} {M : matrix (fin d) (fin d) ℝ} 
  (hU : is_eps_parseval_frame U (4 * ε)) (hM : M.is_diag) (hM' : radial_isotropic (M ⬝ U))
  (hU' : ∀ i : fin n, (1 - γ') * (d / n) ≤ ∥ Uᵀ i ∥^2 ∧ ∥ Uᵀ i ∥^2 ≤ (1 + γ') * (d / n)) :
  matrix (fin d) (fin n) ℝ :=
  λ i j, ((∥ Uᵀ j ∥ / ∥ M.mul_vec (Uᵀ j) ∥) * (M.mul_vec (Uᵀ j) i))


lemma dist_U_W'_bound {ε γ' : ℝ} {U W: matrix (fin d) (fin n) ℝ} {M : matrix (fin d) (fin d) ℝ} 
  (hU : is_eps_parseval_frame U (4 * ε)) (hM : M.is_diag) (hM' : radial_isotropic (M ⬝ U))
  (hU' : ∀ i : fin n, (1 - γ') * (d / n) ≤ ∥ Uᵀ i ∥^2 ∧ ∥ Uᵀ i ∥^2 ≤ (1 + γ') * (d / n)) :
  ∥ U - (W' hU hM hM' hU') ∥^2 ≤ 4 * ε * d^2 + γ' * d^2 :=
begin


end 

lemma dist_U_W_bound {ε γ' : ℝ} {U W: matrix (fin d) (fin n) ℝ} {M : matrix (fin d) (fin d) ℝ} 
  (hU : is_eps_parseval_frame U (4 * ε)) (hM : M.is_diag) (hM' : radial_isotropic (M ⬝ U))
  (hW : W = real.sqrt (d / n) • norm_columns (M ⬝ U))
  (hU' : ∀ i : fin n, (1 - γ') * (d / n) ≤ ∥ Uᵀ i ∥^2 ∧ ∥ Uᵀ i ∥^2 ≤ (1 + γ') * (d / n)) :
  ∥ U - W ∥^2 ≤ 8 * ε * d^2 + 4 * γ' * d^2 :=
begin
  sorry,

end 

theorem nearby_parseval_frame_apply_is_nearby {ε : ℝ} (U : matrix (fin d) (fin n) ℝ) 
  (hU : is_eps_parseval_frame U ε) : 
    ∥ U - nearby_parseval_frame U hU ∥^2 ≤ 20 * ε * d :=
begin
  sorry
end