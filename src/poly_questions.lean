import data.polynomial.basic
import topology.metric_space.basic
import data.polynomial.eval
import data.mv_polynomial.basic
import data.real.basic
import topology.basic
import data.polynomial.ring_division
import topology.instances.real
import data.set.prod
import mv_poly_partials

open_locale polynomial classical

lemma finset_has_min_dif (S : set ℝ) (hS : S.finite) : ∃ ε : ℝ, ε > 0 ∧ ∀ x y : ℝ, x ∈ S → y ∈ S → y ≠ x → |x - y| > ε :=
begin
  by_cases S.nonempty,
  let f : (ℝ × ℝ) → ℝ := λ xy, if xy.1 = xy.2 then 1 else |xy.1 - xy.2|,
  have hf : ∀ x y : ℝ, f (x, y) ≠ 0 :=
  begin
    intros x y,
    simp only [f],
    rw ne,
    rw ite_eq_iff,
    simp only [abs_eq_zero, false_or, not_and, one_ne_zero, and_false],
    intros h1 h2,
    rw sub_eq_zero at h2,
    exact h1 h2,
  end,

  have hf' : ∀ x y : ℝ, f(x, y) ≥ 0 :=
  begin
    simp only [f],
    intros x y,
    split_ifs,
    simp only [zero_le_one, ge_iff_le],
    exact abs_nonneg _,
  end,

  let diffs₂ := f '' (S ×ˢ S),
  have hdiffs₂ : diffs₂.finite := set.finite.image f (set.finite.prod hS hS),
  have : set.nonempty (S ×ˢ S):=
  begin
    rw set.prod_nonempty_iff,
    exact ⟨h, h⟩,
  end,
  have h'diffs₂ : hdiffs₂.to_finset.nonempty :=
  begin
    simp only [set.nonempty_image_iff, set.finite.to_finset.nonempty],
    exact this,
  end,

  have : (0 : ℝ) ∉ diffs₂ :=
  begin
    by_contra,
    rw set.mem_image at h,
    choose x hx using h,
    exact hf x.1 x.2 hx.2,
  end,

  have : ∀ x : ℝ, x ∈ diffs₂ → 0 < x :=
  begin
    intros x hx,
    rw set.mem_image at hx,
    choose a ha using hx,
    rw ← ha.2,
    apply lt_of_le_of_ne,
    exact hf' _ _,
    exact (hf _ _).symm,
  end,

  let δ := hdiffs₂.to_finset.min' h'diffs₂,
  have hδ : δ ∈ diffs₂ :=
  begin
    have : δ ∈ hdiffs₂.to_finset := finset.min'_mem hdiffs₂.to_finset _,
    rw set.finite.mem_to_finset at this,
    exact this,
  end, 

  have hδ' : 0 < δ := this δ hδ,
  use δ / 2,
  split,
  linarith,
  intros x y hx hy hxy,
  have : | x - y | = f (x,y) :=
  begin
    simp only [f],
    split_ifs,
    by_contra,
    simp at h_1,
    exact hxy h_1.symm,
    simp only [eq_self_iff_true],
  end,
  rw this,
  have : f (x,y) ∈ diffs₂ :=
  begin
    simp only [set.mem_image, prod.exists],
    use x,
    use y,
    simp only [and_true, eq_self_iff_true, set.prod_mk_mem_set_prod_eq],
    exact ⟨hx, hy⟩,
  end,
  have : δ ≤ f(x ,y) :=
  begin
    apply finset.min'_le _ _ _,
    rw set.finite.mem_to_finset,
    exact this,
  end,
  linarith,
  use 1,
  simp only [true_and, gt_iff_lt, zero_lt_one],
  intros x y hx hy hxy,
  by_contra h',
  have : S = ∅ :=
  begin
    rw ← set.not_nonempty_iff_eq_empty,
    exact h,
  end,
  rw this at hx,
  rw set.mem_empty_eq at hx,
  exact hx,
end

lemma compl_finset_dense_in_R (S : finset ℝ) : dense (↑S : set ℝ)ᶜ :=
begin
  rw dense,
  intro x,
  rw real.mem_closure_iff,
  intros ε hε,
  by_cases hx : x ∈ S,
  have := finset_has_min_dif ↑S S.finite_to_set,
  choose δ hδ using this,
  by_cases δ < ε,
  use x + δ,
  split,
  simp only [set.mem_compl_eq, finset.mem_coe],
  intro hxδ,
  have foo : x + δ ≠ x :=
  begin
    simp only [add_right_eq_self, ne.def],
    exact ne_of_gt hδ.1,
  end,
  have := hδ.2 x (x + δ) hx hxδ foo,
  simp only [gt_iff_lt, sub_add_cancel', abs_neg] at this,
  rw abs_of_pos hδ.1 at this,
  linarith,
  simp only [add_tsub_cancel_left],
  rw abs_of_pos hδ.1,
  exact h,
  use x + ε / 2,
  split,
  rw not_lt at h,
  simp only [set.mem_compl_eq, finset.mem_coe],
  intro hxε,
  have foo : x + ε / 2 ≠ x :=
  begin
    linarith,
  end,
  have := hδ.2 x (x + ε/2) hx hxε foo,
  simp only [gt_iff_lt, sub_add_cancel', abs_neg] at this,
  have hε' : ε / 2 > 0 :=
  begin
    apply div_pos,
    exact hε,
    simp only [zero_lt_bit0, zero_lt_one],
  end,
  rw abs_of_pos hε' at this,
  linarith,
  simp only [add_tsub_cancel_left],
  have hε' : ε / 2 > 0 :=
  begin
    apply div_pos,
    exact hε,
    simp only [zero_lt_bit0, zero_lt_one],
  end,
  rw abs_of_pos hε',
  linarith,
  use x,
  simp only [abs_zero, set.mem_compl_eq, finset.mem_coe, sub_self],
  exact ⟨ hx, hε ⟩,
end

lemma poly_nonzero_dense {σ : Type*} {p : ℝ[X]} (hp : p ≠ 0) :
  dense {x : ℝ | polynomial.eval x p ≠ 0} :=
begin
  simp_rw ne,
  simp_rw ← polynomial.is_root.def,
  have fact₁ : ↑(polynomial.roots p).to_finset = {x : ℝ | p.is_root x} :=
  begin
    ext,
    simp only [multiset.mem_to_finset, set.mem_set_of_eq, finset.mem_coe],
    rw polynomial.mem_roots,
    exact hp,
  end,
  have fact₂ : {x : ℝ | ¬ p.is_root x} = {x : ℝ | p.is_root x}.compl :=
  begin
    ext,
    simp only [set.compl_eq_compl, iff_self, set.mem_set_of_eq, set.mem_compl_eq],
  end,
  rw fact₂,
  rw ← fact₁,
  -- simp [set.compl_eq_univ_diff],
  -- exact dense.diff_finset (dense_univ) _,
  exact compl_finset_dense_in_R _,
end

lemma poly_in_ball_eq_zero_eq_zero {σ : Type*} (r : ℝ)
  [fintype σ]
  {p : mv_polynomial σ ℝ}
  (hp : p ≠ 0)
  (H : r > 0)
  (h : ¬(metric.ball (0 : σ → ℝ) r ∩
            {y : σ → ℝ | (mv_polynomial.eval y) p ≠ 0}).nonempty) :
  p = 0 :=
begin
  rw ← mv_poly_along_line_eq_zero_iff_mv_poly_eq_zero p,
  by_contra h1,
  simp only [not_forall] at h1,
  choose y hy using h1,
  have dense_nonzero_y := @poly_nonzero_dense σ _ hy,
  by_cases hy' : y = 0,
  simp_rw [eval_along_line_eq_eval, hy', smul_zero] at dense_nonzero_y,
  rw [set.nonempty, not_exists] at h,
  specialize h y,
  rw hy' at h,
  simp only [norm_zero, set.mem_inter_eq, not_and, mem_ball_zero_iff, set.mem_set_of_eq] at h,
  specialize h H,
  rw not_ne_iff at h,
  rw [h] at dense_nonzero_y,
  simp [set.set_of_false] at dense_nonzero_y,
  rw [dense, closure_empty] at dense_nonzero_y,
  specialize dense_nonzero_y 0,
  rw set.mem_empty_eq at dense_nonzero_y,
  exact dense_nonzero_y,
  
  have : ∀ t : ℝ, |t| * ∥ y ∥ < r → (mv_poly_along_line p y).eval t = 0 :=
  begin
    intros t ht,
    rw eval_along_line_eq_eval,
    have : t • y ∈ metric.ball (0 : σ → ℝ) r :=
    begin
      rw mem_ball_zero_iff,
      rw norm_smul,
      rw real.norm_eq_abs,
      exact ht,
    end,
    rw set.nonempty at h,
    rw not_exists at h,
    specialize h (t • y),
    simp only [set.mem_inter_eq, not_and, set.mem_set_of_eq] at h,
    rw not_ne_iff at h,
    exact h this,
  end,
  rw dense at dense_nonzero_y,
  simp_rw real.mem_closure_iff at dense_nonzero_y,
  specialize dense_nonzero_y 0 (r / ∥ y ∥) (by {ring, apply mul_pos, simp only [norm_pos_iff, ne.def, inv_pos], exact hy', exact H}),
  choose t' ht' using dense_nonzero_y,
  simp only [sub_zero, set.mem_set_of_eq] at ht',
  specialize this t' (by {rw ← lt_div_iff, exact ht'.2, simp only [norm_pos_iff, ne.def, hy', not_false_iff],}), --ht'.2,
  exact ht'.1 this,
end

lemma mvpoly_nonzero_dense {σ : Type*} [fintype σ] {p : mv_polynomial σ ℝ} (hp : p ≠ 0) :
  dense {x : σ → ℝ | mv_polynomial.eval x p ≠ 0} := 
begin
  rw metric.dense_iff,
  intros,
  by_contra,
  have : ¬ (metric.ball (0 : σ → ℝ) r ∩ {y : σ → ℝ | (mv_polynomial.eval y) (p.recenter (-x)) ≠ (0 : ℝ)}).nonempty :=
  begin
    rw [set.nonempty, not_exists],
    rw [set.nonempty, not_exists] at h,
    intro y,
    simp only [set.mem_inter_eq, not_and, mem_ball_zero_iff, set.mem_set_of_eq],
    intro hy,
    rw mv_polynomial.recenter_eval,
    simp only [not_not, ne.def, sub_neg_eq_add],
    specialize h (y + x),
    simp only [metric.mem_ball, set.mem_inter_eq, not_and, set.mem_set_of_eq] at h,
    rw dist_eq_norm at h,

    simp only [not_not, ne.def] at h,
    apply h,
    simp only [add_sub_cancel],
    exact hy,
  end,
  have hp' := poly_in_ball_eq_zero_eq_zero r _ H this,
  rw mv_polynomial.eq_zero_iff_recenter_eq_zero at hp',
  exact hp hp',
  intro hp',
  rw mv_polynomial.eq_zero_iff_recenter_eq_zero at hp',
  exact hp hp',

end