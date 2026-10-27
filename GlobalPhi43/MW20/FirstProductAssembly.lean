/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import GlobalPhi43.MW20.FirstProductCoherence
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Assembling the first MW20 product after reconstruction

The tested first germ and its actual reconstruction error give the v²J product
bound with the two local terms. The compact-test adapter derives integrability
from smooth fields. The reconstruction error is still an explicit upstream
input: this module does not certify Theorem 2.8 or the full Lemma 2.9 port.
-/

public section

open MeasureTheory
open scoped ContDiff

namespace GlobalPhi43.MW20

/-- Testing (5.10) at a fixed base point, with the two necessary integrability
facts. This also derives integrability of the tested germ. -/
theorem firstProductGerm_tested_value {E : Type*} [MeasurableSpace E]
    (μ : Measure E) (K v Z J : E → ℝ) (x : E)
    (hJ : Integrable (fun y => K y * J y) μ)
    (hB : Integrable (fun y => K y * ((Z x - Z y) * J y)) μ) :
    Integrable (fun y => K y * firstProductGerm v Z J x y) μ ∧
      (∫ y, K y * firstProductGerm v Z J x y ∂μ) =
        v x ^ 2 * (∫ y, K y * J y ∂μ) +
        2 * v x * (∫ y, K y * ((Z x - Z y) * J y) ∂μ) := by
  have hid (y : E) : K y * firstProductGerm v Z J x y =
      v x ^ 2 * (K y * J y) + 2 * v x * (K y * ((Z x - Z y) * J y)) := by
    have hbase : firstProductGerm v Z J x y =
        v x ^ 2 * J y + 2 * v x * (Z x - Z y) * J y := by
      linarith only [firstProductGerm_decomposition v Z J x y]
    rw [hbase]
    ring
  have hi : Integrable (fun y => v x ^ 2 * (K y * J y) +
      2 * v x * (K y * ((Z x - Z y) * J y))) μ :=
    (hJ.const_mul (v x ^ 2)).add (hB.const_mul (2 * v x))
  refine ⟨(integrable_congr (Filter.Eventually.of_forall hid)).2 hi, ?_⟩
  rw [integral_congr_ae (Filter.Eventually.of_forall hid),
    integral_add (hJ.const_mul _) (hB.const_mul _), integral_const_mul, integral_const_mul]

/-- Conditional reconstruction-to-product adapter, retaining the two explicit
local terms and their factors. The input `hrec` is the actual integral of the
reconstruction error, not a bound on an unrelated scalar. -/
theorem firstProductGerm_product_bound {E : Type*} [MeasurableSpace E]
    (μ : Measure E) (K v Z J : E → ℝ) (x : E)
    (hP : Integrable (fun y => K y * (v y ^ 2 * J y)) μ)
    (hJ : Integrable (fun y => K y * J y) μ)
    (hB : Integrable (fun y => K y * ((Z x - Z y) * J y)) μ)
    {R M j b : ℝ}
    (hrec : |∫ y, K y * (firstProductGerm v Z J x y - v y ^ 2 * J y) ∂μ| ≤ R)
    (hv : |v x| ≤ M) (hj : |∫ y, K y * J y ∂μ| ≤ j)
    (hb : |∫ y, K y * ((Z x - Z y) * J y) ∂μ| ≤ b) :
    |∫ y, K y * (v y ^ 2 * J y) ∂μ| ≤ R + M ^ 2 * j + 2 * M * b := by
  obtain ⟨hiF, hF⟩ := firstProductGerm_tested_value μ K v Z J x hJ hB
  have herr : (∫ y, K y * (firstProductGerm v Z J x y - v y ^ 2 * J y) ∂μ) =
      (∫ y, K y * firstProductGerm v Z J x y ∂μ) -
      (∫ y, K y * (v y ^ 2 * J y) ∂μ) := by
    simp_rw [mul_sub]
    exact integral_sub hiF hP
  have hid : (∫ y, K y * (v y ^ 2 * J y) ∂μ) =
      -(∫ y, K y * (firstProductGerm v Z J x y - v y ^ 2 * J y) ∂μ) +
      v x ^ 2 * (∫ y, K y * J y ∂μ) +
      2 * v x * (∫ y, K y * ((Z x - Z y) * J y) ∂μ) := by
    rw [herr, hF]
    ring
  have hvpow : |v x ^ 2| ≤ M ^ 2 := by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) hv 2
  have hlocal : |v x ^ 2 * (∫ y, K y * J y ∂μ)| ≤ M ^ 2 * j := by
    rw [abs_mul]
    exact mul_le_mul hvpow hj (abs_nonneg _) (sq_nonneg _)
  have h2v : |2 * v x| ≤ 2 * M := by
    simpa only [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] using
      mul_le_mul_of_nonneg_left hv (by norm_num : (0 : ℝ) ≤ 2)
  have hBlocal : |2 * v x * (∫ y, K y * ((Z x - Z y) * J y) ∂μ)| ≤ 2 * M * b := by
    rw [abs_mul]
    exact mul_le_mul h2v hb (abs_nonneg _) ((abs_nonneg _).trans h2v)
  rw [hid]
  exact (abs_add_le _ _).trans
    (add_le_add ((abs_add_le _ _).trans (add_le_add (by simpa only [abs_neg] using hrec)
      hlocal)) hBlocal)

end GlobalPhi43.MW20

end
