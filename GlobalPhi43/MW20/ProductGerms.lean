/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Tactic.Ring

/-!
# The first product germ in MW20 §5.2.2

The germ (5.10) retains the one-leaf tree J and the integrated cubic tree Z
as distinct fields. Its exact coherence identity is the algebraic input to the
smooth reconstruction application. These identities hold without regularity;
the eventual analytic port must retain the standing smoothness convention.
-/

public section

open scoped ContDiff

namespace GlobalPhi43.MW20

variable {E : Type*}

/-- MW20 (5.10) in the project's distinct aliases. -/
def firstProductGerm (v Z J : E → ℝ) (x y : E) : ℝ :=
  v x ^ 2 * J y + 2 * v x * (Z x - Z y) * J y

/-- The diagonal is the product from Lemma 2.9, including J. -/
@[simp] theorem firstProductGerm_diag (v Z J : E → ℝ) (x : E) :
    firstProductGerm v Z J x x = v x ^ 2 * J x := by
  simp [firstProductGerm]


/-- Exact decomposition used before applying the triangle inequality in (2.32).
The first two terms are the tested germ and its reconstruction error; the last
term is the recentered composite B of (2.18). -/
theorem firstProductGerm_decomposition (v Z J : E → ℝ) (x y : E) :
    v y ^ 2 * J y =
      (v y ^ 2 * J y - firstProductGerm v Z J x y) +
      v x ^ 2 * J y + 2 * v x * (Z x - Z y) * J y := by
  unfold firstProductGerm
  ring

/-- The standing smoothness convention is preserved by the actual product germ.
This supplies the smooth F carrier required when (5.10) is passed to Theorem 2.8. -/
theorem firstProductGerm_contDiff [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v Z J : E → ℝ) (hv : ContDiff ℝ ∞ v) (hZ : ContDiff ℝ ∞ Z)
    (hJ : ContDiff ℝ ∞ J) :
    ContDiff ℝ ∞ (fun p : E × E => firstProductGerm v Z J p.1 p.2) := by
  change ContDiff ℝ ∞ (fun p : E × E =>
    v p.1 ^ 2 * J p.2 + 2 * v p.1 * (Z p.1 - Z p.2) * J p.2)
  exact (((hv.comp contDiff_fst).pow 2).mul (hJ.comp contDiff_snd)).add
    (((contDiff_const.mul (hv.comp contDiff_fst)).mul
      ((hZ.comp contDiff_fst).sub (hZ.comp contDiff_snd))).mul (hJ.comp contDiff_snd))

/-- Testing the coherence identity against either kernel orientation. Only the
two integrability facts needed for the Bochner sum are assumed; in the MW20
application they follow from smooth fields and compactly supported tests. -/
theorem firstProductGerm_tested_increment [MeasurableSpace E]
    (μ : MeasureTheory.Measure E) (K v Z J : E → ℝ) (x₁ x₂ : E)
    (hJ : MeasureTheory.Integrable (fun y => K y * J y) μ)
    (hB : MeasureTheory.Integrable (fun y => K y * ((Z x₂ - Z y) * J y)) μ) :
    (∫ y, K y * (firstProductGerm v Z J x₁ y - firstProductGerm v Z J x₂ y) ∂μ) =
      ((v x₁ + v x₂) * ((v x₁ + Z x₁) - (v x₂ + Z x₂)) +
        (v x₁ - v x₂) * (Z x₁ - Z x₂)) * (∫ y, K y * J y ∂μ) +
      2 * (v x₁ - v x₂) * (∫ y, K y * ((Z x₂ - Z y) * J y) ∂μ) := by
  let a := (v x₁ + v x₂) * ((v x₁ + Z x₁) - (v x₂ + Z x₂)) +
    (v x₁ - v x₂) * (Z x₁ - Z x₂)
  let b := 2 * (v x₁ - v x₂)
  have hid : ∀ y, K y * (firstProductGerm v Z J x₁ y - firstProductGerm v Z J x₂ y) =
      a * (K y * J y) + b * (K y * ((Z x₂ - Z y) * J y)) := by
    intro y
    dsimp [a, b, firstProductGerm]
    ring
  calc
    _ = ∫ y, a * (K y * J y) + b * (K y * ((Z x₂ - Z y) * J y)) ∂μ :=
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hid)
    _ = _ := by
      rw [MeasureTheory.integral_add (hJ.const_mul a) (hB.const_mul b),
        MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]

end GlobalPhi43.MW20

end
