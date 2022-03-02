import data.matrix.basic
import data.real.basic
import analysis.normed_space.basic

variables {n : ℕ} {d : ℕ}

/-- This is a fake eigenvalue function on matrices...
It _will_ be set up this way, and likely return meaningless values for non-self-adjoint matrices-/
def eigs (A : matrix (fin d) (fin d) ℝ) : finset ℝ := sorry 

lemma eigs_smul_ext {x : ℝ} (c : ℝ) (A : matrix (fin d) (fin d) ℝ) (h : x ≠ 0): 
  x ∈ eigs (A) ↔ (c * x) ∈ (eigs (c • A)) := sorry

-- lemma eigs_smul (c : ℝ) (A : matrix (fin d) (fin d) ℝ) : eigs (c • A) = c • (eigs (A)) := sorry

lemma eigs_zero (d : ℕ) : eigs (0 : matrix (fin d) (fin d) ℝ) = {(0 : ℝ)} :=
begin
  ext,
  have h0 : (0 : matrix (fin d) (fin d) ℝ) = (0 : ℝ) • (0 : matrix (fin d) (fin d) ℝ) :=
    (smul_zero 0).symm,
  split,

  intro h1,
  -- rw h0 at h1,
  rw finset.mem_singleton,
  by_contra,
  have : ∀ b : ℝ, b ∈ eigs 0 :=
    begin
      intro b,
      rw eigs_smul_ext (b / a) 0 h at h1,
      rw smul_zero at h1,
      field_simp at h1,
      exact h1,
    end,
  sorry,
  rw finset.mem_singleton,
  sorry,
  -- change a ≠ 0 at h,
  -- rw eigs_smul_ext 0 0 a at h,
  -- rw h0,
  -- rw eigs_smul_ext 0 0 a,
end

def is_psd (U : matrix (fin d) (fin d) ℝ) : Prop := ∀ (x : ℝ), x ∈ eigs U → 0 ≤ x

def is_pd (U : matrix (fin d) (fin d) ℝ) : Prop := ∀ x : ℝ, x ∈ eigs U → 0 < x

lemma psd_zero (d : ℕ) : is_psd (0 : matrix (fin d) (fin d) ℝ) :=
begin
  intros x hx,
  rw eigs_zero at hx,
  rw finset.mem_singleton at hx,
  rw hx,
end

lemma not_pd_zero (d : ℕ) : ¬ is_pd (0 : matrix (fin d) (fin d) ℝ) :=
begin
  change ¬ (∀ x : ℝ, x ∈ eigs 0 → 0 < x),
  rw not_forall,
  simp_rw [not_imp, not_lt],
  use 0,
  rw eigs_zero,
  rw finset.mem_singleton,
  simp only [le_refl, eq_self_iff_true, and_self],
end

lemma psd_add_of_psd_of_psd {A B : matrix (fin d) (fin d) ℝ} (hA : is_psd A) (hB : is_psd B) : is_psd (A + B) := sorry

lemma not_psd_of_neg_pd {A : matrix (fin d) (fin d) ℝ} (hA : is_pd (-A)) : ¬(is_psd A) := sorry

lemma psd_of_pd {A : matrix (fin d) (fin d) ℝ} (hA : is_pd A) : is_psd A := sorry

lemma pd_of_psd_of_not_neg_psd {A : matrix (fin d) (fin d) ℝ} (hA : is_psd A) (hA' : ¬(is_psd (-A))) : is_pd A := sorry

lemma eq_zero_of_psd_of_neg_psd {A : matrix (fin d) (fin d) ℝ} (hA : is_psd A) (hA' : is_psd (-A)) : A = 0 := sorry

instance : partial_order (matrix (fin d) (fin d) ℝ) :=
{ le := λ a b, is_psd (b - a),
  lt := λ a b, is_pd (b - a),
  le_refl := 
  begin
    intro a,
    change is_psd (a - a),
    rw sub_self,
    exact psd_zero _,
  end,
  le_trans := 
  begin
    intros a b c hab hbc,
    change is_psd (c - a),
    have : c - a = (c - b) + (b - a) := by simp only [sub_add_sub_cancel, sub_left_inj],
    rw this,
    exact psd_add_of_psd_of_psd hbc hab,
  end,
  lt_iff_le_not_le := 
  begin
    intros a b,
    split,
    intro hab,
    change is_pd (b - a) at hab,
    split,
    exact psd_of_pd hab,
    change ¬(is_psd (a - b)),
    exact not_psd_of_neg_pd hab,
    intro h,
    have fact₁ := h.1,
    have fact₂ : ¬ (is_psd (-(b - a))) := h.2,
    exact pd_of_psd_of_not_neg_psd fact₁ fact₂,
  end,
  le_antisymm :=
  begin
    intros a b hab hba,
    have : a - b = 0 := eq_zero_of_psd_of_neg_psd hab hba,
    rw sub_eq_zero at this,
    exact this,
  end,}