import data.real.sqrt
import data.real.sign
import linear_algebra.matrix.is_diag
import analysis.inner_product_space.basic
import radial_isotropic
import psd
import perturbation
import analysis.special_functions.pow
import majorization
import arithmetic_bounds
import data.real.nnreal

open_locale big_operators matrix

variables {n d: ℕ} (hnd : (n : ℝ) * (d : ℝ) ≠ (0 : ℝ))
variables {V : matrix (fin d) (fin n) ℝ} {ε : ℝ}
variables {v : (fin n) → ℝ}

def to_pi (f : ℕ → ℝ) : (fin n → ℝ) := λ i, f i

def to_N_to_R (f : fin n → ℝ) : ℕ → ℝ := λ i, if h : i < n then (f (fin.mk i h)) else 0

lemma to_N_to_R_to_to_pi (f : fin n → ℝ) : to_pi (to_N_to_R f) = f :=
begin
  ext,
  rw to_N_to_R,
  rw to_pi,
  simp only [dite_eq_ite, dif_ctx_congr, fin.mk_eq_subtype_mk, fin.eta, ite_eq_left_iff],
  intro h,
  exfalso,
  exact h (subtype.prop x),
end

noncomputable instance fro : has_norm (matrix (fin d) (fin n) ℝ) :=
{
  norm := λ M, real.sqrt(∑ j : fin n, ∑ i : fin d, M i j^2),
}

noncomputable instance : has_norm (fin n → ℝ) :=
{
  norm := λ v, real.sqrt(∑ j : fin n, |v j|^2 ),
}

instance : has_inner ℝ (fin n → ℝ) :=
{
  inner := λ u v, ∑ i : fin n, (u i) * (v i)
}

lemma norm_is_euclidean (v : fin n → ℝ) : ∥ v ∥^2 = ⟪ v , v ⟫_ℝ :=
begin
  simp only [norm, inner],
  rw real.sq_sqrt,
  congr,
  ext,
  simp only [pow_bit0_abs],
  simp_rw [sq, ← real.coe_nnabs, sq, ← nnreal.coe_mul, ← nnreal.coe_sum],
  exact nnreal.coe_nonneg _,
end

notation `⟪`x`, `y`⟫` := @inner ℝ _ _ x y


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

noncomputable def V_norm (V : matrix (fin d) (fin n) ℝ) := (real.sqrt(d / n)) • norm_columns(V)
noncomputable def η (ε : ℝ) (V : matrix (fin d) (fin n) ℝ): fin n → fin d → ℝ := perturbations ε (V_norm V)ᵀ
noncomputable def U (ε : ℝ) (V : matrix (fin d) (fin n) ℝ):= (V_norm V) + (η ε V)ᵀ

lemma bound_1 {ε : ℝ} (hnd : (n : ℝ) * d ≠ 0) (V : matrix (fin d) (fin n) ℝ) 
  (hV : is_eps_parseval_frame V ε) : ∀ i : fin n, ∥ (U ε V)ᵀ i - Vᵀ i ∥^2 ≤
    (real.sqrt(d / n) - real.sqrt((1 - ε) * d / n))^2 + ∥ η ε V i ∥^2 + 2 * ∥ η ε V i ∥ :=
begin
  intro i,
  -- have h1 : ∥ η ε V i ∥₂^2 ≤ ε :=
  --   calc ∥ η ε V i ∥₂^2 = ∥ perturbations ε (V_norm V)ᵀ i ∥₂^2 : by {congr}
  --     ...         ≤ ε : perturbations_bound ε (V_norm V)ᵀ i,
  rw [← real_inner_self_eq_norm_sq],

  rw [real_inner_sub_sub_self, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq],
  simp only [U],
  rw [matrix.transpose_add, pi.add_apply, matrix.transpose_transpose, to_euclidean.map_add],
  have h2 := (norm_add_le (to_euclidean ((V_norm V)ᵀ i)) (to_euclidean (η ε V i))),
  rw ← abs_eq_self.2 (norm_nonneg (to_euclidean ((V_norm V)ᵀ i) + to_euclidean ((η ε V i)))) at h2,
  rw ← abs_eq_self.2 (add_nonneg (norm_nonneg (to_euclidean ((V_norm V)ᵀ i) )) _) at h2,
  have h3 := sq_le_sq h2,
  clear h2,
  suffices : (∥ ((V_norm V)ᵀ i) ∥ + ∥(η ε V i) ∥)^2 
    - 2 * ⟪ ((V_norm V)ᵀ i) + (η ε V i), (Vᵀ i)⟫ + ∥ (Vᵀ i) ∥^2 ≤ 
    (real.sqrt(d / n) - real.sqrt((1 - ε) * d / n))^2 + ∥ to_euclidean (η ε V i) ∥^2 + 2 * ∥ to_euclidean (η ε V i) ∥,
    { apply (le_trans _ this),
    apply add_le_add,
    apply sub_le_sub,
    exact h3,
    exact le_refl _,
    exact le_refl _,
    },
  rw add_sq,
  simp only [V_norm],
  rw matrix.transpose_smul,
  rw pi.smul_apply,
  rw to_euclidean.map_smul,
  rw norm_smul,
  rw norm_columns_apply,
  
end,


theorem nearby_parseval_frame_is_parseval {ε : ℝ} (hnd : (n : ℝ) * d ≠ 0) (V : matrix (fin d) (fin n) ℝ) 
  (hV : is_eps_parseval_frame V ε) : is_parseval_frame (nearby_parseval_frame V hV) :=
begin

  have h1 : ∀ i : fin n, ∥ (U ε V)ᵀ i - Vᵀ i ∥₂^2 ≤
    (real.sqrt(d / n) - real.sqrt((1 - ε) * d / n))^2 + ∥ η ε V i ∥₂^2 + 2 * ∥ η ε V i ∥₂ := bound_1 hnd V hV,
  
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

noncomputable def W' (U : matrix (fin d) (fin n) ℝ) (M : matrix (fin d) (fin d) ℝ) :
  matrix (fin d) (fin n) ℝ :=
  λ i j, ((∥ Uᵀ j ∥ / ∥ M.mul_vec (Uᵀ j) ∥) * (M.mul_vec (Uᵀ j) i))


-- Note, u^2 means u squared entrywise
lemma w'_sq_maj_u_sq {ε γ' : ℝ} {U W: matrix (fin d) (fin n) ℝ} {M : matrix (fin d) (fin d) ℝ} 
  (hU : is_eps_parseval_frame U (4 * ε)) (hM : M.is_diag) (hM' : radial_isotropic (M ⬝ U))
  (hM'' : ∀ i j : fin d, i ≥ j → M i i ≥ M j j)
  (hU' : ∀ i : fin n, (1 - γ') * (d / n) ≤ ∥ Uᵀ i ∥^2 ∧ ∥ Uᵀ i ∥^2 ≤ (1 + γ') * (d / n)) :
  ∀ i : fin n,  majorizes (((W' U M)ᵀ i)^2) (Uᵀ i) :=
begin
  sorry,
end 

lemma dist_U_W'_bound {ε γ' : ℝ} {U W: matrix (fin d) (fin n) ℝ} {M : matrix (fin d) (fin d) ℝ} 
  (hU : is_eps_parseval_frame U (4 * ε)) (hM : M.is_diag) (hM' : radial_isotropic (M ⬝ U))
  (hM'' : ∀ i j : fin d, i ≥ j → M i i ≥ M j j) (hM''' : ∀ i : fin d, M i i ≥ 0)
  (hU' : ∀ i : fin n, (1 - γ') * (d / n) ≤ ∥ Uᵀ i ∥^2 ∧ ∥ Uᵀ i ∥^2 ≤ (1 + γ') * (d / n)) :
  ∥ U - (W' U M) ∥^2 ≤ 4 * ε * d^2 + γ' * d^2 :=
begin
  calc ∥ U - (W' U M) ∥^2 = ∑ j : fin n, ∑ i : fin d, ((U i j - (W' U M) i j)^2) : by 
  { simp only [norm], rw real.sq_sqrt, congr,
  conv_rhs {
    congr,
    skip,
    funext,
    

  }
  }
  ... ≤ 4 * ε * d^2 + γ' * d^2 : by {},

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