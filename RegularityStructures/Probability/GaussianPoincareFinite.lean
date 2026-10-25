/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.FiniteTensorization
public import RegularityStructures.Probability.GaussianPoincareClosure
public import RegularityStructures.Probability.GaussianPolynomial

/-!
# Finite-dimensional Gaussian Poincare: slice infrastructure

The product proof uses the first-coordinate decomposition of a finite product Gaussian.  The
lemmas below make the corresponding `Fin.cons` derivative and polynomial-growth calculations
explicit.  The resulting induction is the finite-dimensional form used for the covariance and
white-noise estimates (Hairer--Steele, Definition 2.20 and Remark 2.22).
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Real

namespace RegularityStructures

def finCons {n : ℕ} (x : ℝ) (y : Fin n → ℝ) : Fin (n + 1) → ℝ :=
  @Fin.cons n (fun _ : Fin (n + 1) => ℝ) x y

lemma norm_fin_cons_le {n : ℕ} (x : ℝ) (y : Fin n → ℝ) :
    ‖finCons x y‖ ≤ ‖x‖ + ‖y‖ := by
  change ‖@Fin.cons n (fun _ : Fin (n + 1) => ℝ) x y‖ ≤ ‖x‖ + ‖y‖
  rw [Pi.norm_def]
  have hsup :
      (Finset.univ.sup fun b : Fin (n + 1) =>
        ‖(@Fin.cons n (fun _ : Fin (n + 1) => ℝ) x y) b‖₊) ≤ ‖x‖₊ + ‖y‖₊ := by
    apply Finset.sup_le
    intro i hi
    by_cases h : i = 0
    · subst i
      simp only [Fin.cons_zero]
      exact le_add_of_nonneg_right (by positivity)
    · rw [show i = (i.pred h).succ by exact (Fin.succ_pred i h).symm]
      simp only [Fin.cons_succ]
      have hreal : ‖y (i.pred h)‖ ≤ ‖x‖ + ‖y‖ :=
        (norm_le_pi_norm y _).trans (le_add_of_nonneg_left (norm_nonneg _))
      exact_mod_cast hreal
  have hreal :
      (↑(Finset.univ.sup fun b : Fin (n + 1) =>
        ‖(@Fin.cons n (fun _ : Fin (n + 1) => ℝ) x y) b‖₊) : ℝ) ≤
        ↑(‖x‖₊ + ‖y‖₊) := by
    exact_mod_cast hsup
  simpa using hreal

lemma hasFDerivAt_fin_cons_scalar {n : ℕ} (y : Fin n → ℝ) (x : ℝ) :
    HasFDerivAt (fun t : ℝ => finCons t y)
      (ContinuousLinearMap.single ℝ (fun _ : Fin (n + 1) => ℝ) 0) x := by
  have hpi : HasFDerivAt (fun t : ℝ => fun i => finCons t y i)
      (ContinuousLinearMap.pi (fun i : Fin (n + 1) =>
        (ContinuousLinearMap.proj i).comp
          (ContinuousLinearMap.single ℝ (fun _ : Fin (n + 1) => ℝ) 0))) x := by
    rw [hasFDerivAt_pi]
    intro i
    by_cases hi : i = 0
    · subst i
      have heq : (ContinuousLinearMap.proj (0 : Fin (n + 1))).comp
          (ContinuousLinearMap.single ℝ (fun _ : Fin (n + 1) => ℝ) 0) =
          (1 : ℝ →L[ℝ] ℝ) := by
        apply ContinuousLinearMap.ext
        intro t
        simp [ContinuousLinearMap.single_apply]
      rw [heq]
      have hfun : (fun t : ℝ => finCons t y 0) = id := by
        funext t
        simp [finCons]
      rw [hfun]
      convert hasFDerivAt_id x using 1
    · have hpred : ∀ t : ℝ, finCons t y i = y (i.pred hi) := by
        intro t
        calc
          finCons t y i = finCons t y ((i.pred hi).succ) := by
            exact congrArg (finCons t y) (Fin.succ_pred i hi).symm
          _ = y (i.pred hi) := by
            simpa [finCons] using
              (@Fin.cons_succ n (fun _ : Fin (n + 1) => ℝ) t y (i.pred hi))
      have heq : (ContinuousLinearMap.proj i).comp
          (ContinuousLinearMap.single ℝ (fun _ : Fin (n + 1) => ℝ) 0) = 0 := by
        apply ContinuousLinearMap.ext
        intro t
        simp [ContinuousLinearMap.single_apply, hi]
      rw [heq]
      have hfun : (fun t : ℝ => finCons t y i) = fun _ => y (i.pred hi) := by
        funext t
        exact hpred t
      rw [hfun]
      exact hasFDerivAt_const _ x
  have heq : ContinuousLinearMap.pi (fun i : Fin (n + 1) =>
      (ContinuousLinearMap.proj i).comp
        (ContinuousLinearMap.single ℝ (fun _ : Fin (n + 1) => ℝ) 0)) =
      ContinuousLinearMap.single ℝ (fun _ : Fin (n + 1) => ℝ) 0 := by
    apply ContinuousLinearMap.ext
    intro t
    apply funext
    intro i
    simp [ContinuousLinearMap.single_apply]
  rw [heq] at hpi
  exact hpi

lemma fderiv_fin_cons_scalar {n : ℕ} {f : (Fin (n + 1) → ℝ) → ℝ}
    (hcont : ContDiff ℝ 1 f) (x : ℝ) (y : Fin n → ℝ) :
    fderiv ℝ (fun t : ℝ => f (finCons t y)) x 1 =
      fderiv ℝ f (finCons x y) (Pi.single 0 1) := by
  have h := (hcont.differentiable one_ne_zero (finCons x y)).hasFDerivAt.comp
    x (hasFDerivAt_fin_cons_scalar y x)
  have h' := h.fderiv
  simpa [Function.comp_def, ContinuousLinearMap.single_apply] using congrArg (fun L => L 1) h'

lemma polynomial_bound_fin_cons_scalar {n : ℕ} {f : (Fin (n + 1) → ℝ) → ℝ}
    {C : ℝ} {N : ℕ} (hC : 0 ≤ C)
    (hgrowth : ∀ x : Fin (n + 1) → ℝ,
      |f x| ≤ C * (1 + ‖x‖) ^ N) (y : Fin n → ℝ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ x : ℝ,
      |f (finCons x y)| ≤ D * (1 + |x|) ^ N := by
  refine ⟨C * (1 + ‖y‖) ^ N, mul_nonneg hC (by positivity), ?_⟩
  intro x
  have hxy : 1 + ‖finCons x y‖ ≤ (1 + ‖x‖) * (1 + ‖y‖) := by
    have hnorm := norm_fin_cons_le x y
    have hnonneg : 0 ≤ ‖x‖ := norm_nonneg _
    have hy : 0 ≤ ‖y‖ := norm_nonneg _
    nlinarith
  have hpow : (1 + ‖finCons x y‖) ^ N ≤
      ((1 + ‖x‖) * (1 + ‖y‖)) ^ N := by
    exact pow_le_pow_left₀ (by positivity) hxy N
  calc
    |f (finCons x y)| ≤ C * (1 + ‖finCons x y‖) ^ N := hgrowth _
    _ ≤ C * ((1 + ‖x‖) * (1 + ‖y‖)) ^ N :=
      mul_le_mul_of_nonneg_left hpow hC
    _ = C * (1 + ‖y‖) ^ N * (1 + |x|) ^ N := by
      rw [mul_pow]
      ring_nf
      rw [Real.norm_eq_abs]
      ring

lemma polynomial_bound_fin_cons_rest {n : ℕ} {f : (Fin (n + 1) → ℝ) → ℝ}
    {C : ℝ} {N : ℕ} (hC : 0 ≤ C)
    (hgrowth : ∀ x : Fin (n + 1) → ℝ,
      |f x| ≤ C * (1 + ‖x‖) ^ N) (x : ℝ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ y : Fin n → ℝ,
      |f (finCons x y)| ≤ D * (1 + ‖y‖) ^ N := by
  refine ⟨C * (1 + ‖x‖) ^ N, mul_nonneg hC (by positivity), ?_⟩
  intro y
  have hxy : 1 + ‖finCons x y‖ ≤ (1 + ‖x‖) * (1 + ‖y‖) := by
    have hnorm := norm_fin_cons_le x y
    have hnonneg : 0 ≤ ‖x‖ := norm_nonneg _
    have hy : 0 ≤ ‖y‖ := norm_nonneg _
    nlinarith
  have hpow : (1 + ‖finCons x y‖) ^ N ≤
      ((1 + ‖x‖) * (1 + ‖y‖)) ^ N := by
    exact pow_le_pow_left₀ (by positivity) hxy N
  calc
    |f (finCons x y)| ≤ C * (1 + ‖finCons x y‖) ^ N := hgrowth _
    _ ≤ C * ((1 + ‖x‖) * (1 + ‖y‖)) ^ N :=
      mul_le_mul_of_nonneg_left hpow hC
    _ = C * (1 + ‖x‖) ^ N * (1 + ‖y‖) ^ N := by
      rw [mul_pow]
      ring

end RegularityStructures

end
