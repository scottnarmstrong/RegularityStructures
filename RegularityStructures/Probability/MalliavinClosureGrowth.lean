/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.GaussianPolynomialAlgebra
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import RegularityStructures.Probability.StandardGaussianIBP

/-!
# Growth of compactly supported smooth tests

Compactly supported smooth coefficient functions have bounded value and first derivative.  The
result is recorded in the polynomial-growth format used by the finite-dimensional Gaussian IBP
theorems, so that no growth condition is hidden in a later application.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory

namespace RegularityStructures

open scoped ContDiff in
theorem malliavin_compact_contDiff_polynomial_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : E → ℝ} (hsupport : HasCompactSupport u) (hcont : ContDiff ℝ ∞ u) :
    ∃ K : ℝ, ∃ M : ℕ, 0 ≤ K ∧
      ∀ x : E, |u x| + ‖fderiv ℝ u x‖ ≤ K * (1 + ‖x‖) ^ M := by
  obtain ⟨C, hC, hbound⟩ := hsupport.exists_bound_iteratedFDeriv hcont 1
  have hvalue (x : E) : ‖u x‖ ≤ C := by
    simpa using hbound 0 (by norm_num) x
  have hderiv (x : E) : ‖fderiv ℝ u x‖ ≤ C := by
    simpa [norm_iteratedFDeriv_one] using hbound 1 (by norm_num) x
  refine ⟨2 * C, 0, by positivity, ?_⟩
  intro x
  calc
    |u x| + ‖fderiv ℝ u x‖ ≤ C + C := by
      exact add_le_add (by simpa [Real.norm_eq_abs] using hvalue x) (hderiv x)
    _ = 2 * C * (1 + ‖x‖) ^ 0 := by ring_nf

theorem malliavin_product_contDiff_polynomial_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f u : E → ℝ} (hcont_f : ContDiff ℝ 1 f) (hcont_u : ContDiff ℝ 1 u)
    (hgrowth_f : ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧
      ∀ x : E, |f x| + ‖fderiv ℝ f x‖ ≤ C * (1 + ‖x‖) ^ N)
    (hgrowth_u : ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧
      ∀ x : E, |u x| + ‖fderiv ℝ u x‖ ≤ C * (1 + ‖x‖) ^ N) :
    ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧
      ∀ x : E, |f x * u x| + ‖fderiv ℝ (fun y => f y * u y) x‖ ≤
        C * (1 + ‖x‖) ^ N := by
  rcases hgrowth_f with ⟨C, N, hC, hf⟩
  rcases hgrowth_u with ⟨D, M, hD, hu⟩
  let r : E → ℝ := fun x => 1 + ‖x‖
  have hr (x : E) : 0 ≤ r x := by
    dsimp [r]
    positivity
  have hfr (x : E) : |f x| ≤ C * r x ^ N := by
    dsimp [r]
    exact (le_add_of_nonneg_right (norm_nonneg _)).trans (hf x)
  have hfur (x : E) : |u x| ≤ D * r x ^ M := by
    dsimp [r]
    exact (le_add_of_nonneg_right (norm_nonneg _)).trans (hu x)
  have hfd (x : E) : fderiv ℝ (fun y => f y * u y) x =
      f x • fderiv ℝ u x + u x • fderiv ℝ f x := by
    exact ((hcont_f.differentiable one_ne_zero x).hasFDerivAt.mul
      (hcont_u.differentiable one_ne_zero x).hasFDerivAt).fderiv
  have hvalue (x : E) : |f x * u x| ≤ C * D * r x ^ (N + M) := by
    have hp : 0 ≤ r x ^ N := pow_nonneg (hr x) _
    have hq : 0 ≤ r x ^ M := pow_nonneg (hr x) _
    calc
      |f x * u x| = |f x| * |u x| := abs_mul _ _
      _ ≤ (C * r x ^ N) * (D * r x ^ M) := by
        exact mul_le_mul (hfr x) (hfur x) (abs_nonneg _) (by positivity)
      _ = C * D * r x ^ (N + M) := by
        calc
          C * r x ^ N * (D * r x ^ M) = C * D * (r x ^ N * r x ^ M) := by ring
          _ = C * D * r x ^ (N + M) := by rw [← pow_add]
  have hderiv (x : E) : ‖fderiv ℝ (fun y => f y * u y) x‖ ≤
      2 * (C * D) * r x ^ (N + M) := by
    have hp : 0 ≤ r x ^ N := pow_nonneg (hr x) _
    have hq : 0 ≤ r x ^ M := pow_nonneg (hr x) _
    rw [hfd]
    calc
      ‖f x • fderiv ℝ u x + u x • fderiv ℝ f x‖ ≤
          ‖f x • fderiv ℝ u x‖ + ‖u x • fderiv ℝ f x‖ := norm_add_le _ _
      _ = |f x| * ‖fderiv ℝ u x‖ + |u x| * ‖fderiv ℝ f x‖ := by
        simp [norm_smul, Real.norm_eq_abs]
      _ ≤ (C * r x ^ N) * (D * r x ^ M) +
          (D * r x ^ M) * (C * r x ^ N) := by
        have hdu : ‖fderiv ℝ u x‖ ≤ D * r x ^ M :=
          (le_add_of_nonneg_left (abs_nonneg (u x))).trans (by simpa [r] using hu x)
        have hdf : ‖fderiv ℝ f x‖ ≤ C * r x ^ N :=
          (le_add_of_nonneg_left (abs_nonneg (f x))).trans (by simpa [r] using hf x)
        apply add_le_add
        · exact mul_le_mul (hfr x) hdu (norm_nonneg _) (by positivity)
        · exact mul_le_mul (hfur x) hdf (norm_nonneg _) (by positivity)
      _ = 2 * (C * D) * r x ^ (N + M) := by
        calc
          C * r x ^ N * (D * r x ^ M) + D * r x ^ M * (C * r x ^ N) =
              2 * (C * D) * (r x ^ N * r x ^ M) := by ring
          _ = 2 * (C * D) * r x ^ (N + M) := by rw [← pow_add]
  refine ⟨3 * (C * D), N + M, by positivity, ?_⟩
  intro x
  dsimp [r] at hvalue hderiv ⊢
  calc
    |f x * u x| + ‖fderiv ℝ (fun y => f y * u y) x‖ ≤
        C * D * (1 + ‖x‖) ^ (N + M) +
          2 * (C * D) * (1 + ‖x‖) ^ (N + M) :=
      add_le_add (hvalue x) (hderiv x)
    _ = 3 * (C * D) * (1 + ‖x‖) ^ (N + M) := by ring

theorem malliavin_comp_continuousLinearMap_polynomial_bound
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : E → ℝ} {L : F →L[ℝ] E} (hcont : ContDiff ℝ 1 g)
    (hgrowth : ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧
      ∀ x : E, |g x| + ‖fderiv ℝ g x‖ ≤ C * (1 + ‖x‖) ^ N) :
    ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧
      ∀ z : F, |g (L z)| + ‖fderiv ℝ (fun y => g (L y)) z‖ ≤
        C * (1 + ‖z‖) ^ N := by
  rcases hgrowth with ⟨C, N, hC, hg⟩
  let K : ℝ := max 1 ‖L‖
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  have hKone : 1 ≤ K := by
    exact le_max_left _ _
  have hLnorm : ‖L‖ ≤ K := by
    exact le_max_right _ _
  let r : F → ℝ := fun z => 1 + ‖z‖
  have hr (z : F) : 0 ≤ r z := by
    dsimp [r]
    positivity
  have hbase (z : F) : 1 + ‖L z‖ ≤ K * r z := by
    calc
      1 + ‖L z‖ ≤ 1 + ‖L‖ * ‖z‖ := by
        gcongr
        exact L.le_opNorm z
      _ ≤ K + K * ‖z‖ := by
        gcongr
      _ = K * r z := by ring
  have hpow (z : F) : (1 + ‖L z‖) ^ N ≤ (K * r z) ^ N := by
    exact pow_le_pow_left₀ (by positivity) (hbase z) N
  have hfd (z : F) : fderiv ℝ (fun y => g (L y)) z =
      (fderiv ℝ g (L z)).comp L := by
    exact ((hcont.differentiable one_ne_zero (L z)).hasFDerivAt.comp z L.hasFDerivAt).fderiv
  have hvalue (z : F) : |g (L z)| ≤ C * K ^ N * r z ^ N := by
    have hbase' := hpow z
    have hbound : |g (L z)| ≤ C * (K * r z) ^ N := by
      exact ((le_add_of_nonneg_right (norm_nonneg _)).trans (hg (L z))).trans
        (mul_le_mul_of_nonneg_left hbase' hC)
    calc
      |g (L z)| ≤ C * (K * r z) ^ N := hbound
      _ = C * K ^ N * r z ^ N := by rw [mul_pow]; ring
  have hderiv (z : F) : ‖fderiv ℝ (fun y => g (L y)) z‖ ≤
      C * K ^ N * r z ^ N * ‖L‖ := by
    rw [hfd]
    calc
      ‖(fderiv ℝ g (L z)).comp L‖ ≤ ‖fderiv ℝ g (L z)‖ * ‖L‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (C * (1 + ‖L z‖) ^ N) * ‖L‖ := by
        gcongr
        exact (le_add_of_nonneg_left (abs_nonneg (g (L z)))).trans (hg (L z))
      _ ≤ (C * (K * r z) ^ N) * ‖L‖ := by
        gcongr
        exact hbase z
      _ = C * K ^ N * r z ^ N * ‖L‖ := by rw [mul_pow]; ring
  refine ⟨C * K ^ N * (1 + ‖L‖), N, by positivity, ?_⟩
  intro z
  dsimp [r] at hvalue hderiv ⊢
  calc
    |g (L z)| + ‖fderiv ℝ (fun y => g (L y)) z‖ ≤
        C * K ^ N * (1 + ‖z‖) ^ N +
          C * K ^ N * (1 + ‖z‖) ^ N * ‖L‖ :=
      add_le_add (hvalue z) (hderiv z)
    _ = C * K ^ N * (1 + ‖L‖) * (1 + ‖z‖) ^ N := by ring

end RegularityStructures

end
