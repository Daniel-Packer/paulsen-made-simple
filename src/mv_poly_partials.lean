import data.polynomial.basic
import data.polynomial.eval
import data.mv_polynomial.basic
import data.real.basic
import topology.basic
import data.polynomial.ring_division
import topology.instances.real
import analysis.special_functions.pow
import data.set.prod
import data.polynomial.eval
import data.finsupp.pointwise
import data.mv_polynomial.funext

-- you have a polynomial p that is 0 in a neighborhood N of the origin. 
-- pick any nonzero v in N and consider the single variable polynomial p(tv) in t
-- by your previous stuff, this is identically 0
-- in general, if you want to know what p(x) is for any x, 
-- take a small enough r so that rx is in N, then consider the single variable polynomial p(trx)
--  and observe that it's zero, so p(x)=p((1/r)rx)=0

open_locale polynomial classical big_operators

variables {σ : Type*} [fintype σ] (P : mv_polynomial σ ℝ)

noncomputable def mv_poly_along_line (P : mv_polynomial σ ℝ) (v : σ → ℝ) : ℝ[X] :=
{
  to_finsupp :=
  ∑ exps : σ →₀ ℕ in P.support, finsupp.single (∑ i : σ, exps i) (P.coeff exps * ∏ i : σ, (v i)^(exps i)),
}

noncomputable def mv_polynomial.recenter (P : mv_polynomial σ ℝ) (v : σ → ℝ) : mv_polynomial σ ℝ :=
mv_polynomial.eval₂ mv_polynomial.C (λ i, mv_polynomial.X i - mv_polynomial.C (v i)) P

lemma mv_polynomial.recenter_eval (P : mv_polynomial σ ℝ) (v₀ v₁ : σ → ℝ) :
  mv_polynomial.eval v₁ (mv_polynomial.recenter P v₀) = mv_polynomial.eval (v₁ - v₀) P :=
begin
  rw mv_polynomial.recenter,
  rw mv_polynomial.eval₂_eq,
  rw mv_polynomial.eval_sum,
  simp only [mv_polynomial.eval_C, map_mul, finset.sum_congr],
  simp_rw mv_polynomial.eval_prod,
  simp only [mv_polynomial.eval_X, map_pow, mv_polynomial.eval_C, finset.prod_congr, finset.sum_congr, map_sub],
  rw mv_polynomial.eval_eq,
  simp only [eq_self_iff_true, finset.prod_congr, finset.sum_congr, pi.sub_apply],
end

lemma mv_polynomial.eq_zero_of_recenter_eq_zero (P : mv_polynomial σ ℝ) (v₀ : σ → ℝ) :
  P.recenter v₀ = 0 → P = 0 :=
begin
  intro h,
  rw mv_polynomial.funext_iff,
  intro x,
  rw mv_polynomial.funext_iff at h,
  specialize h (x + v₀),
  rw mv_polynomial.recenter_eval at h,
  simp only [add_sub_cancel, map_zero] at h,
  rw h,
  simp only [eq_self_iff_true, map_zero],
end

lemma mv_polynomial.eq_zero_iff_recenter_eq_zero (P : mv_polynomial σ ℝ) (v₀ : σ → ℝ) :
  P.recenter v₀ = 0 ↔ P = 0 :=
begin
  split,
  exact mv_polynomial.eq_zero_of_recenter_eq_zero P v₀,
  intro h,
  rw mv_polynomial.funext_iff,
  intro x,
  rw mv_polynomial.recenter_eval,
  rw h,
  simp only [eq_self_iff_true, map_zero],
end

lemma sum_supported_foo (P Q : mv_polynomial σ ℝ) (v : σ → ℝ) (n : ℕ) : 
  ∑ (x : σ →₀ ℕ) in ((P + Q).support \ P.support),
    (finsupp.single (finset.univ.sum x) (mv_polynomial.coeff x P * ∏ (i : σ), v i ^ x i)) n = 0 :=
begin
  apply finset.sum_eq_zero,
  intros x hx,
  simp only [mv_polynomial.coeff_add, not_not, finset.mem_sdiff, ne.def, mv_polynomial.mem_support_iff] at hx,
  rw hx.2,
  simp only [finsupp.coe_zero, zero_mul, pi.zero_apply, eq_self_iff_true, finsupp.single_zero],
end

lemma in_supp_not_add_supp (P Q : mv_polynomial σ ℝ) (x : σ →₀ ℕ) :
  x ∈ (P.support \ (Q + P).support) → mv_polynomial.coeff x P = - mv_polynomial.coeff x Q :=
begin
  intro h,
  simp only [mv_polynomial.coeff_add, not_not, finset.mem_sdiff, ne.def, mv_polynomial.mem_support_iff] at h,
  rw add_comm at h,
  rw ← add_eq_zero_iff_eq_neg,
  exact h.2,
end

lemma in_supp_not_add_supp' (P Q : mv_polynomial σ ℝ) (v : σ → ℝ) (n : ℕ) (x : σ →₀ ℕ) :
  x ∈ (P.support \ (Q + P).support) → 
    finsupp.single (finset.univ.sum x) (mv_polynomial.coeff x P * ∏ (i : σ), v i ^ x i)
    n
    = - finsupp.single (finset.univ.sum x) (mv_polynomial.coeff x Q * ∏ (i : σ), v i ^ x i)
    n :=
begin
  intro h,
  rw in_supp_not_add_supp P Q x h,
  simp only [finsupp.single_neg, neg_mul, pi.neg_apply, eq_self_iff_true, neg_inj, finsupp.coe_neg],
end

lemma supp_minus_add_supp_eq_supp_minus_add_supp (P Q : mv_polynomial σ ℝ) :
  (P.support \ (Q + P).support) = (Q.support \ (Q + P).support) :=
begin
  ext,
  simp only [mv_polynomial.coeff_add,
 not_not,
 and.congr_left_iff,
 finset.mem_sdiff,
 ne.def,
 mv_polynomial.mem_support_iff],
 intro h,
 rw add_eq_zero_iff_neg_eq at h,
 simp_rw ← h,
 simp only [iff_self, neg_eq_zero],
end

lemma mv_poly_along_line_add (P Q : mv_polynomial σ ℝ) (v : σ → ℝ) : 
  mv_poly_along_line (P + Q) v = mv_poly_along_line P v + mv_poly_along_line Q v :=
begin
  iterate { rw mv_poly_along_line,},
  apply polynomial.ext,
  intro n,
  rw polynomial.add_to_finsupp,
  iterate {rw polynomial.coeff,},
  rw finsupp.add_apply,
  iterate {rw finsupp.finset_sum_apply,},
  simp_rw mv_polynomial.coeff_add,
  simp_rw add_mul,
  simp_rw finsupp.single_add,
  simp_rw finsupp.coe_add,
  simp_rw pi.add_apply,
  rw finset.sum_add_distrib,
  rw ← finset.sum_inter_add_sum_diff (P + Q).support P.support,
  rw sum_supported_foo P Q,
  rw ← finset.sum_inter_add_sum_diff (P + Q).support Q.support,
  rw add_comm P Q,
  rw sum_supported_foo Q P,
  rw add_zero,
  rw add_zero,
  have hP : P.support = (P.support \ (Q + P).support) ∪ (P.support ∩ (Q + P).support) := (finset.sdiff_union_inter _ _).symm,
  have hQ : Q.support = (Q.support \ (P + Q).support) ∪ (Q.support ∩ (P + Q).support) := (finset.sdiff_union_inter _ _).symm,
  conv_rhs {rw hP, rw hQ},
  rw finset.sum_union,
  rw finset.sum_union,
  rw finset.inter_comm _ P.support,
  rw finset.inter_comm _ Q.support,
  conv_rhs {rw add_assoc, rw add_comm, rw add_assoc,},
  rw add_right_inj _,
  conv_rhs {rw add_assoc, rw add_comm, rw add_comm P Q, rw add_assoc},
  apply self_eq_add_right.2,
  rw finset.sum_congr rfl (in_supp_not_add_supp' P Q v n),
  rw supp_minus_add_supp_eq_supp_minus_add_supp,
  simp only [eq_self_iff_true, add_left_neg, finset.sum_neg_distrib],
  rw disjoint_iff,
  simp only [finset.inf_eq_inter, finset.bot_eq_empty],
  rw finset.inter_comm,
  simp only [finset.inter_assoc, finset.inter_sdiff_self, eq_self_iff_true, finset.inter_empty],
  rw disjoint_iff,
  simp only [finset.inf_eq_inter, finset.bot_eq_empty],
  rw finset.inter_comm,
  simp only [finset.inter_assoc, finset.inter_sdiff_self, eq_self_iff_true, finset.inter_empty],
end

lemma ite_fact (a b : ℝ) : ite (0 = 0) a b = a := 
begin
  simp only [if_true, eq_self_iff_true],
end

lemma mv_polynomial.support_C (a : ℝ) : ((mv_polynomial.C a): mv_polynomial σ ℝ).support = ite (a = 0) ∅ {0} :=
begin
  rw mv_polynomial.C_apply,
  rw mv_polynomial.support_monomial,
end

lemma mv_polynomial.support_C' (a : ℝ) (ha : a ≠ 0) : ((mv_polynomial.C a): mv_polynomial σ ℝ).support = {0} :=
begin
  rw mv_polynomial.C_apply,
  rw mv_polynomial.support_monomial,
  simp only [ite_eq_right_iff],
  intro h,
  exfalso,
  exact ha h,
end

lemma mv_polynomial.pairwise_induction_on {M : mv_polynomial σ ℝ → mv_polynomial σ ℝ → Prop} (P Q : mv_polynomial σ ℝ)
  (h_mono : ∀ (u₁ u₂ : σ →₀ ℕ) (a₁ a₂ : ℝ), M (mv_polynomial.monomial u₁ a₁) (mv_polynomial.monomial u₂ a₂))
  (h_add₁ : ∀ p₁ p₂ q : mv_polynomial σ ℝ, M p₁ q → M p₂ q → M (p₁ + p₂) q) 
  (h_add₂ : ∀ p q₁ q₂ : mv_polynomial σ ℝ, M p q₁ → M p q₂ → M p (q₁ + q₂)) :
  M P Q :=
begin
  apply mv_polynomial.induction_on' P,
  apply mv_polynomial.induction_on' Q,
  exact λ u a v b, h_mono v u b a,
  intros p q hp hq u a,
  have := h_add₂ (mv_polynomial.monomial u a) p q _ _,
  exact this,
  exact hp _ _,
  exact hq _ _,
  intros p q hp hq,
  have := h_add₁ p q Q _ _,
  exact this,
  exact hp,
  exact hq,
end

lemma mv_polynomial.pairwise_induction_on' {M : mv_polynomial σ ℝ → mv_polynomial σ ℝ → Prop} (P Q : mv_polynomial σ ℝ)
  (h_mono : ∀ (u₁ u₂ : σ →₀ ℕ) (a₁ a₂ : ℝ), M (mv_polynomial.monomial u₁ a₁) (mv_polynomial.monomial u₂ a₂))
  (h_add : ∀ p₁ p₂ q₁ q₂ : mv_polynomial σ ℝ, M p₁ p₂ → M q₁ q₂ → M (p₁ + q₁) (p₂ + q₂)) :
  M P Q :=
begin
  apply mv_polynomial.induction_on' P,
  apply mv_polynomial.induction_on' Q,
  exact λ u a v b, h_mono v u b a,
  intros p q hp hq u a,
  have := h_add (mv_polynomial.monomial u a) p 0 q _ _,
  rw add_zero at this,
  exact this,
  exact hp _ _,
  rw [← mv_polynomial.C_0, mv_polynomial.C_apply],
  exact hq 0 0,
  intros p q hp hq,
  have := h_add p Q q 0 _ _,
  rw add_zero at this,
  exact this,
  exact hp,
  apply mv_polynomial.induction_on' q,
  intros u a,
  rw [← mv_polynomial.C_0, mv_polynomial.C_apply],
  exact h_mono _ _ _ _,
  intros p q hp hq,
  have := h_add p 0 q 0 _ _,
  rw add_zero at this,
  exact this,
  exact hp,
  exact hq,
end

lemma mv_poly_along_line_mul (P Q : mv_polynomial σ ℝ) (v : σ → ℝ) : 
  mv_poly_along_line (P * Q) v = mv_poly_along_line P v * mv_poly_along_line Q v :=
begin
  apply mv_polynomial.pairwise_induction_on P Q,
  intros,

  rw mv_polynomial.monomial_mul,
  iterate{rw mv_poly_along_line,},
  rw polynomial.mul_to_finsupp,
  iterate{rw mv_polynomial.support_monomial},
  by_cases ha₁ : a₁ = 0,
  rw ha₁,
  simp only [mv_polynomial.monomial_zero, if_true, mv_polynomial.coeff_monomial, mv_polynomial.coeff_zero, zero_mul,
 eq_self_iff_true, finsupp.single_zero, ite_mul, finset.sum_const_zero, finset.sum_congr],
  by_cases ha₂ : a₂ = 0,
  rw ha₂,
  simp only [mv_polynomial.monomial_zero, if_true, mv_polynomial.coeff_monomial, mv_polynomial.coeff_zero, zero_mul,
 eq_self_iff_true, finsupp.single_zero, ite_mul, finset.sum_const_zero, finset.sum_congr],
  simp only [if_t_t, if_true, zero_mul, eq_self_iff_true, finsupp.single_zero, finset.sum_const_zero, mul_zero, finset.sum_congr],
  have ha₁₂ : a₁ * a₂ ≠ 0 := mul_ne_zero ha₁ ha₂,
  simp only [ha₁, ha₂, if_false, mul_ne_zero, ha₁₂],
  iterate {rw finset.sum_singleton,},
  rw add_monoid_algebra.single_mul_single,
  iterate {rw mv_polynomial.coeff_monomial,},
  simp only [if_true, eq_self_iff_true],
  simp only [pi.add_apply, finsupp.coe_add, finset.sum_congr],
  rw finset.sum_add_distrib,
  congr' 1,
  iterate {rw ←  mul_assoc,},
  conv_rhs {rw mul_comm _ a₂},
  iterate {rw mul_assoc},
  rw ← finset.prod_mul_distrib,
  simp_rw ← pow_add,
  iterate {rw ← mul_assoc},
  rw mul_comm a₁ a₂,
  
  intros p₁ p₂ q h₁ h₂,
  rw add_mul,
  iterate {rw mv_poly_along_line_add},
  rw h₁,
  rw h₂,
  rw add_mul,
  intros p q₁ q₂ h₁ h₂,
  rw mul_add,
  iterate {rw mv_poly_along_line_add},
  rw mul_add,
  rw h₁,
  rw h₂,
end

def eval_along_line_eq_eval' (P : mv_polynomial σ ℝ) : Prop :=
  ∀ (v : σ → ℝ) (t : ℝ), (mv_poly_along_line P v).eval t = mv_polynomial.eval (t • v) P

lemma eval_along_line_eq_eval'_cons : ∀ r : ℝ, eval_along_line_eq_eval' (@mv_polynomial.C ℝ σ _ r) :=
begin
  intro r,
  rw eval_along_line_eq_eval',
  intros v t,
  rw mv_polynomial.eval_eq,
  rw mv_poly_along_line,
  rw polynomial.eval_eq_sum,
  simp only [finset.prod_const_one,
 finsupp.coe_zero,
 mul_one,
 algebra.id.smul_eq_mul,
 zero_mul,
 pi.zero_apply,
 mv_polynomial.coeff_C,
 ite_mul,
 ne.def,
 finsupp.support_zero,
 finset.prod_congr,
 mv_polynomial.coeff_zero_C,
 pi.smul_apply,
 pow_zero,
 finset.sum_congr,
 finset.sum_ite_eq,
 ite_not,
 mv_polynomial.mem_support_iff],
 split_ifs,
 rw h,
 simp only [if_t_t,
 mv_polynomial.C_0,
 zero_mul,
 finsupp.single_zero,
 finset.sum_const_zero,
 mv_polynomial.support_zero,
 finset.sum_congr],
 change (0 : ℝ[X]).sum (λ (e : ℕ) (a : ℝ), a * t ^ e) = 0,
 rw polynomial.sum_zero_index,
 rw ← mv_polynomial.monomial_zero',
 rw mv_polynomial.support_monomial,
 split_ifs,
 exfalso,
 exact h h_1,
 simp only [finset.prod_const_one,
 finsupp.coe_zero,
 mul_one,
 if_true,
 pi.zero_apply,
 eq_self_iff_true,
 finset.sum_const_zero,
 finset.sum_singleton,
 finset.prod_congr,
 pow_zero,
 finset.sum_congr],

  rw polynomial.sum,
  rw polynomial.support,
  have : (finsupp.single 0 r) 0 ≠ 0 :=
  begin
    simp only [finsupp.single_eq_same, ne.def],
    exact h,
  end,
  rw (finsupp.support_eq_singleton.2 ⟨ this, (by simp only [finsupp.single_eq_same, eq_self_iff_true])⟩),
  simp only [mul_one, finset.sum_singleton, pow_zero],
  rw polynomial.coeff,
  simp only [finsupp.single_eq_same, eq_self_iff_true],
end

lemma eval_along_line_eq_eval'_add : ∀ p q : mv_polynomial σ ℝ, eval_along_line_eq_eval' p → 
    eval_along_line_eq_eval' q → eval_along_line_eq_eval' (p + q) :=
begin
  intros p q hp hq v t,
  simp_rw [mv_poly_along_line_add, polynomial.eval_add],
  rw [hp, hq],
  rw mv_polynomial.eval,
  simp only [add_left_inj, mv_polynomial.coe_eval₂_hom, eq_self_iff_true, mv_polynomial.eval₂_add],
end

lemma eval_along_line_eq_eval'x : ∀ (p : mv_polynomial σ ℝ) (n : σ), 
    eval_along_line_eq_eval' p → eval_along_line_eq_eval' (p * mv_polynomial.X n) :=
begin
  intros p n hp v t,
  rw mv_polynomial.eval,
  simp only [algebra.id.smul_eq_mul,
 mv_polynomial.eval₂_mul,
 mv_polynomial.coe_eval₂_hom,
 pi.smul_apply,
 mv_polynomial.eval₂_X],
 rw mv_poly_along_line_mul,
 rw polynomial.eval_mul,
 rw hp,
 simp_rw mv_polynomial.eval,
 simp only [mv_polynomial.coe_eval₂_hom, mul_eq_mul_left_iff],
 left,
 rw mv_poly_along_line,
 rw polynomial.eval_eq_sum,
 have : (@mv_polynomial.X ℝ σ _ n).support = {finsupp.single n 1} :=
 begin
   rw mv_polynomial.X,
   rw mv_polynomial.support,
   rw mv_polynomial.monomial,
   simp only [finsupp.lsingle_apply],
   apply finsupp.support_eq_singleton.2,
   split,
   simp only [one_ne_zero, finsupp.single_eq_same, ne.def, not_false_iff],
   simp only [finsupp.single_eq_same, eq_self_iff_true],
 end,
 rw this,
 simp only [one_mul, mv_polynomial.coeff_X, finset.sum_singleton],
 rw polynomial.sum,
 simp_rw polynomial.support,
  by_cases hv : v n ≠ 0,
  rw finsupp.support_single_ne_zero _,
  simp only [finset.sum_singleton],
  rw polynomial.coeff,
  simp only [finsupp.single_eq_same],
  simp_rw finsupp.single_apply,
  simp only [finset.mem_univ,
 if_true,
 finset.sum_boole,
 nat.cast_id,
 finset.prod_ite_eq,
 finset.prod_congr,
 pow_boole],
 rw finset.filter_eq,
 simp only [finset.mem_univ, if_true, pow_one, finset.card_singleton],
 rw mul_comm,
 intro H,
 apply hv,
 simp_rw finsupp.single_apply at H,
 simp only [finset.mem_univ, if_true, finset.prod_ite_eq, finset.prod_congr, pow_boole] at H,
 exact H,
 simp only [not_not, ne.def] at hv,
 simp_rw finsupp.single_apply,
 simp only [finset.mem_univ,
 if_true,
 finset.sum_boole,
 nat.cast_id,
 finset.prod_ite_eq,
 finset.prod_congr,
 pow_boole,
 finset.sum_congr],
 rw hv,
 simp only [finset.sum_empty,
 eq_self_iff_true,
 finsupp.single_zero,
 finsupp.support_zero,
 mul_zero,
 finset.sum_congr],
end

lemma eval_along_line_eq_eval (P : mv_polynomial σ ℝ) (v : σ → ℝ) (t : ℝ) : 
  (mv_poly_along_line P v).eval t = mv_polynomial.eval (t • v) P :=
begin
  have hcons : ∀ r : ℝ, eval_along_line_eq_eval' (mv_polynomial.C r) := λ r v t, eval_along_line_eq_eval'_cons r v t,
  have hadd : ∀ p q : mv_polynomial σ ℝ, eval_along_line_eq_eval' p → 
    eval_along_line_eq_eval' q → eval_along_line_eq_eval' (p + q) := eval_along_line_eq_eval'_add, 
  have hx : ∀ (p : mv_polynomial σ ℝ) (n : σ), 
    eval_along_line_eq_eval' p → eval_along_line_eq_eval' (p * mv_polynomial.X n) := eval_along_line_eq_eval'x,

  have := @mv_polynomial.induction_on _ _ _ eval_along_line_eq_eval' P hcons hadd hx, 
  exact this v t,
end

lemma eval_along_line_eq_eval'' (P : mv_polynomial σ ℝ) (v : σ → ℝ): 
  (mv_poly_along_line P v).eval 1 = mv_polynomial.eval (v) P :=
begin
  rw eval_along_line_eq_eval P v 1,
  rw one_smul,
end

lemma mv_poly_along_line_eq_zero_iff_mv_poly_eq_zero (P : mv_polynomial σ ℝ) :
  (∀ (v : σ → ℝ), mv_poly_along_line P v = 0) ↔ P = 0 :=
  begin
    split,
    swap,
    intros hP v,
    rw mv_poly_along_line,
    rw hP,
    simp only [mv_polynomial.coeff_zero, zero_mul, finsupp.single_zero, finset.sum_const_zero, mv_polynomial.support_zero, finset.sum_congr],
    rw polynomial.has_zero,
    intro h,
    apply mv_polynomial.funext,
    intro v,
    rw ← eval_along_line_eq_eval'',
    rw h v,
    rw polynomial.eval_zero,
    simp only [eq_self_iff_true, map_zero],
  end

