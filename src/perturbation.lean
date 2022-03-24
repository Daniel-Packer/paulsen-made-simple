import data.real.basic
import linear_algebra.basic
import linear_algebra.linear_independent
import analysis.normed_space.basic
import analysis.inner_product_space.euclidean_dist
import data.mvpolynomial.basic
import data.polynomial.basic

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
-- variable [finite_dimensional.finrank ℝ M = d] <- Want to include this somehow

def is_perm2 (s : ((fin n) × (fin n)) → fin 2) : Prop := ∃ σ : equiv.perm (fin n), ∀ i j : fin n,
  if j = σ i then s (i, j) = 1 else s (i, j) = 0

def is_perm (s : ((fin n) × (fin n)) → ℕ) : Prop := ∃ σ : equiv.perm (fin n), ∀ i j: fin n, 
  if j = σ i then s (i, j) = 1 else s (i, j) = 0

lemma fun_fin_fin (n : ℕ) : fintype (fin n → fin n) :=
begin
  exact pi.fintype,
end

lemma fun_fin_fin_fin (n : ℕ) : fintype (((fin n) × (fin n)) → fin 2) :=
begin
  apply pi.fintype,
end

def perm_to_fun (s : fin n → fin n) : ((fin n) × (fin n)) → ℕ :=
  λ ij, if (s ij.fst = ij.2) then 1 else 0

def perms (n : ℕ) : set (((fin n) × (fin n)) → ℕ) := (λ x, is_perm x)
def perms2 (n : ℕ) : set (((fin n) × (fin n)) → fin 2) := (λ x, is_perm2 x)

def perms1_to_2 (n : ℕ) : perms n → (perms2 n) :=
begin
  intro s,
  have hs : is_perm ↑s := subtype.coe_prop s,
  let s₀ : ((fin n) × (fin n)) → ℕ := ↑s,
  let s' : ((fin n) × (fin n)) → fin 2 :=
  begin
    intro ij,
    let k := s₀ ij,
    exact k,
  end,
  have : is_perm2 s' :=
  begin
    choose σ hσ using hs,
    have : ∀ i j : fin n, if j = σ i then s' (i, j) = 1 else s' (i, j) = 0 :=
    begin
      intros i j,
      simp only [s', s₀],
      have := hσ i j,
      split_ifs,
      split_ifs at this,
      rw [this, nat.cast_one],
      split_ifs at this,
      rw [this, nat.cast_zero],
    end,
    rw is_perm2,
    use σ,
    exact this,
  end,
  exact {val := s', property := this},
end
def perms2_to_1 (n : ℕ) : perms2 n → (perms n) :=
begin
  intro s,
  have hs : is_perm2 ↑s := subtype.coe_prop s,
  let s₀ : ((fin n) × (fin n)) → fin 2 := ↑s,
  let s' : ((fin n) × (fin n)) → ℕ :=
  begin
    intro ij,
    let := (s₀ ij).val,
    exact this,
  end,
  have : is_perm s' :=
  begin
    choose σ hσ using hs,
    have : ∀ i j : fin n, if j = σ i then s' (i, j) = 1 else s' (i, j) = 0 :=
    begin
      intros i j,
      simp only [s', s₀],
      simp only [fin.val_eq_coe],
      have := hσ i j,
      split_ifs,
      split_ifs at this,
      rw [this, fin.coe_one],
      split_ifs at this,
      rw [this, fin.coe_zero],
    end,
    rw is_perm,
    use σ,
    exact this,
  end,
  exact {val := s', property := this},
end

lemma left_inv (n : ℕ) : function.left_inverse (perms1_to_2 n) (perms2_to_1 n) :=
begin
  intro x,
  rw [perms1_to_2, perms2_to_1],
  simp,
end

lemma perm_val_le_one (s : ((fin n) × (fin n)) → ℕ) (hs : is_perm s) : ∀ ij : (fin n) × (fin n), s ij < 2 :=
begin
  intro ij,
  rw is_perm at hs,
  choose σ hσ using hs,
  specialize hσ ij.1 ij.2,
  split_ifs at hσ,
  calc s ij = s (ij.1, ij.2) : by simp only [prod.mk.eta]
    ...     < 2 : by {rw hσ, simp only [succ_order.succ_le_succ_iff, nat.one_lt_bit0_iff, le_zero_iff],},
  calc s ij = s (ij.1, ij.2) : by simp only [prod.mk.eta]
    ...     < 2 : by {rw hσ, simp only [nat.succ_pos']},
end

lemma right_inv (n : ℕ) : function.right_inverse (perms1_to_2 n) (perms2_to_1 n) :=
begin
  intro s,
  rw [perms1_to_2, perms2_to_1],
  simp only [],
  ext ij,
  have hs : is_perm ↑s := subtype.coe_prop s,
  let s₀ : (fin n) × (fin n) → ℕ := ↑s,
  have : ∀ ij : (fin n) × (fin n), (s₀ ij) % 2 = s₀ ij :=
  begin
    intro ij,
    apply nat.mod_eq_of_lt,
    exact perm_val_le_one s₀ hs ij,
  end,
  simpa using (this ij),
end

def perms_equiv : perms2 n ≃ perms n :=
{
  to_fun := perms2_to_1 n,
  inv_fun := perms1_to_2 n,
  left_inv := left_inv n,
  right_inv := right_inv n,
}

noncomputable instance : fintype (perms n) :=
begin
  apply fintype.of_equiv (perms2 n),
  exact perms_equiv,
end

def perms_3 (n : ℕ) : set (fin n × (fin n) →₀ ℕ) := finsupp.equiv_fun_on_fintype.symm '' (perms n)

def perms_finsupp (n : ℕ) : set (fin n × (fin n) →₀ ℕ) := 
{ s : (fin n × (fin n) →₀ ℕ ) | finsupp.equiv_fun_on_fintype s ∈ perms n }

noncomputable instance : fintype (perms_finsupp n) :=
begin
  rw perms_finsupp,
end

noncomputable instance : fintype (perms_3 n) :=
begin
  rw perms_3,
  apply fintype.of_equiv (perms n),
  exact equiv.image _ _,
end

lemma perms_3_equiv_perms (n : ℕ) : (perms_3 n).to_finset ≃ perms n :=
{
  to_fun := λ s,
  begin
    have := subtype.coe_prop s,
    rw set.mem_def at this,
    simp only [set.mem_to_finset_val] at this,
    rw set.mem_def at this,

  end,
  inv_fun := sorry,
  left_inv := sorry,
  right_inv := sorry,

}
-- begin
--   simp_rw perms_3,
  
-- end


lemma equiv_apply_perms (s : (fin n) × (fin n) →₀ ℕ) : (finsupp.equiv_fun_on_fintype.symm '' (perms n)) s = (perms n) (finsupp.equiv_fun_on_fintype.symm s) :=
begin
  rw ← @set.mem_def _ s (finsupp.equiv_fun_on_fintype.symm '' (perms n)),
  simp only [set.mem_image, finsupp.equiv_fun_on_fintype_symm_coe, eq_iff_iff],
  split,
  intro h,
  choose x hx using h,
  have : x = ⇑s :=
  begin
    rw ← hx.2,
    ext i,
    simp only [finsupp.equiv_fun_on_fintype_symm_apply_to_fun, eq_self_iff_true],
  end,
  rw this at hx,
  exact hx.1,
  intro h,
  use s,
  split,
  exact h,
  simp only [finsupp.equiv_fun_on_fintype_symm_coe, eq_self_iff_true],
end

-- lemma equiv_perms : (finsupp.equiv_fun_on_fintype.symm '' (perms n)) = (perms n) (finsupp.equiv_fun_on_fintype.symm) :=

noncomputable def det_as_poly (n : ℕ) : mv_polynomial ((fin n) × (fin n)) ℝ :=
begin
  let det_poly : mv_polynomial ((fin n) × (fin n)) ℝ :=
  {
    support := (perms_3 n).to_finset,
    to_fun := λ s, if h : (is_perm s) then (by {choose σ hσ using h, exact σ.sign}) else 0,
    mem_support_to_fun := 
    begin
      intro s,
      rw [set.mem_to_finset, set.mem_def, perms_3],
      rw [equiv_apply_perms s, finsupp.equiv_fun_on_fintype_symm_coe, perms],
      simp only [exists_prop, int.cast_eq_zero, and_true, iff_self, units.ne_zero, dif_ctx_congr, exists_prop_congr',
        forall_prop_congr', ne.def, not_false_iff, dite_eq_right_iff, not_forall, coe_coe],
    end,
  },
  exact det_poly,
end

lemma det_as_poly_eq_det (n : ℕ) (M : matrix (fin n) (fin n) ℝ) : mv_polynomial.eval (function.uncurry M) (det_as_poly n) = M.det :=
begin
  -- rw det_as_poly,
  -- simp only [],
  rw mv_polynomial.eval_eq,
  rw matrix.det_apply,
  -- apply finset.sum_bij _ _ _ _ _,
  have hsupport : (det_as_poly n).support ≃ (equiv.perm (fin n)) :=
  {
    to_fun := 
    begin
      change (perms_3 n).to_finset → (equiv.perm (fin n)),
      intro s,
      have := subtype.prop s,
      simp only [set.mem_to_finset] at this,
      rw set.mem_def at this,
      let s' := perms_3_equiv_perms n s,
      have : is_perm ↑s' := subtype.prop s',
      rw is_perm at this,
      choose σ hσ using this,
      exact σ,
    end,
    inv_fun := sorry,
    left_inv := sorry,
    right_inv := sorry,
  }
  -- begin
  --   rw det_as_poly,
  --   change (perms_3 n).to_finset ≃ (equiv.perm (fin n)),
  --   simp_rw [perms_3],
  -- end,
  -- begin
  --   sorry,
  -- end,
  -- rw hsupport,
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
