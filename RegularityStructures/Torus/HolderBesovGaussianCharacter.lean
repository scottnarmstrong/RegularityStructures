/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Torus.HeatKernel
public import Mathlib.Analysis.Fourier.AddCircleMulti
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Fourier characters of the Euclidean heat density

The heat density on `Fin 3 → ℝ` is the product of three centred Gaussian densities of variance `2s`.
Their characteristic functions give the Fourier multiplier of the heat semigroup. This is an input
to the equivalence of the heat norm (2.3) of the statement with the Littlewood--Paley norm.
-/

public noncomputable section

open MeasureTheory Real ProbabilityTheory UnitAddTorus
open scoped NNReal

namespace RegularityStructures

theorem gaussKernel_eq_prod_gaussianPDFReal {s : ℝ} (hs : 0 < s) (y : Fin 3 → ℝ) :
    gaussKernel s y = ∏ i : Fin 3, gaussianPDFReal 0 (2 * Real.toNNReal s) (y i) := by
  have ha : 0 < 4 * π * s := mul_pos (mul_pos (by norm_num) pi_pos) hs
  have hbase : 2 * π * (2 * s) = 4 * π * s := by ring
  have hexp (u : ℝ) : -(u - 0) ^ 2 / (2 * (2 * s)) = -(4 * s)⁻¹ * u ^ 2 := by
    ring
  simp only [gaussKernel_eq_prod, gaussianPDFReal_def, NNReal.coe_mul, NNReal.coe_ofNat,
    Real.coe_toNNReal s hs.le, hbase, hexp,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  rw [sqrt_eq_rpow, ← rpow_neg_one, ← rpow_mul ha.le, ← rpow_natCast,
    ← rpow_mul ha.le]
  congr 1
  norm_num

private theorem integral_pdf_fourier {s : ℝ} (hs : 0 < s) (k : ℤ) :
    (∫ y : ℝ, (gaussianPDFReal 0 (2 * Real.toNNReal s) y : ℂ) *
      fourier k (y : UnitAddCircle)) =
      Complex.exp ((-4 * π ^ 2 * s * (k : ℝ) ^ 2 : ℝ) : ℂ) := by
  let v : ℝ≥0 := 2 * Real.toNNReal s
  have hv : v ≠ 0 := mul_ne_zero (by norm_num) (Real.toNNReal_pos.mpr hs).ne'
  have hc := charFun_gaussianReal (μ := 0) (v := v) (2 * π * (k : ℝ))
  rw [charFun_apply_real, integral_gaussianReal_eq_integral_smul hv] at hc
  calc
    _ = ∫ y : ℝ, gaussianPDFReal 0 v y •
        Complex.exp (((2 * π * (k : ℝ) : ℝ) : ℂ) * (y : ℂ) * Complex.I) := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [fourier_coe_apply, Complex.real_smul]
      congr 1
      congr 1
      push_cast
      ring
    _ = _ := hc
    _ = _ := by
      congr 1
      simp only [v, NNReal.coe_mul, NNReal.coe_ofNat, Real.coe_toNNReal s hs.le]
      push_cast
      ring

theorem integral_gaussKernel_mul_fourierCharacter {s : ℝ} (hs : 0 < s)
    (k : Fin 3 → ℤ) :
    (∫ y : Fin 3 → ℝ, (gaussKernel s y : ℂ) * mFourier k (torusProj y)) =
      ∏ i : Fin 3, Complex.exp ((-4 * π ^ 2 * s * (k i : ℝ) ^ 2 : ℝ) : ℂ) := by
  simp only [gaussKernel_eq_prod_gaussianPDFReal hs, Complex.ofReal_prod,
    mFourier, ContinuousMap.coe_mk, torusProj, ← Finset.prod_mul_distrib]
  rw [integral_fintype_prod_volume_eq_prod (fun i : Fin 3 => fun y : ℝ =>
    (gaussianPDFReal 0 (2 * Real.toNNReal s) y : ℂ) * fourier (k i) (y : UnitAddCircle))]
  exact Finset.prod_congr rfl fun i _ => integral_pdf_fourier hs (k i)

end RegularityStructures

end
