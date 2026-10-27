/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import GlobalPhi43.MW20.ProductGerms
public import Mathlib.Tactic.Linarith

/-!
# Tested coherence bound for the first MW20 product germ

This is the triangle-inequality step in §5.2.2, applied to the actual weighted
integral of the germ (5.10). The six constituent bounds are the application
sites for the source's local Hölder and recentered tree seminorms. No kernel
or reconstruction theorem is postulated here.
-/

public section

open MeasureTheory

namespace GlobalPhi43.MW20

/-- The three tested coherence terms, with the explicit factors of two retained.
In the source application `A` bounds the increment of v+Z, `B` the increment of
v, `C` the increment of Z, and `j,b` the J and recentered-ZJ tests. -/
theorem firstProductGerm_tested_increment_bound {E : Type*} [MeasurableSpace E]
    (μ : Measure E) (K v Z J : E → ℝ) (x₁ x₂ : E)
    (hJ : Integrable (fun y => K y * J y) μ)
    (hB : Integrable (fun y => K y * ((Z x₂ - Z y) * J y)) μ)
    {M A B C j b : ℝ}
    (hv₁ : |v x₁| ≤ M) (hv₂ : |v x₂| ≤ M)
    (hA : |(v x₁ + Z x₁) - (v x₂ + Z x₂)| ≤ A)
    (hv : |v x₁ - v x₂| ≤ B) (hZ : |Z x₁ - Z x₂| ≤ C)
    (hj : |∫ y, K y * J y ∂μ| ≤ j)
    (hb : |∫ y, K y * ((Z x₂ - Z y) * J y) ∂μ| ≤ b) :
    |∫ y, K y * (firstProductGerm v Z J x₁ y - firstProductGerm v Z J x₂ y) ∂μ| ≤
      2 * M * A * j + B * C * j + 2 * B * b := by
  have hprod : ∀ {a₁ a₂ c₁ c₂ : ℝ}, |a₁| ≤ c₁ → |a₂| ≤ c₂ →
      |a₁ * a₂| ≤ c₁ * c₂ := by
    intro a₁ a₂ c₁ c₂ ha₁ ha₂
    rw [abs_mul]
    exact mul_le_mul ha₁ ha₂ (abs_nonneg _) ((abs_nonneg _).trans ha₁)
  have hsum : |v x₁ + v x₂| ≤ 2 * M := by
    have h := (abs_add_le (v x₁) (v x₂)).trans (add_le_add hv₁ hv₂)
    linarith
  have h₁ := hprod (hprod hsum hA) hj
  have h₂ := hprod (hprod hv hZ) hj
  have h₃ := hprod (hprod (show |(2 : ℝ)| ≤ 2 by norm_num) hv) hb
  rw [firstProductGerm_tested_increment μ K v Z J x₁ x₂ hJ hB, add_mul]
  exact (abs_add_le _ _).trans
    (add_le_add ((abs_add_le _ _).trans (add_le_add h₁ h₂)) h₃)

/-- The source-scale version of the first coherence bound. The exponents of
the three terms are those used in MW20 §5.2.2; the repeated spatial powers in
the middle term are combined exactly, rather than bounded with an extra loss. -/
theorem firstProductGerm_coherence_scales {E : Type*} [MeasurableSpace E]
    (μ : Measure E) (K v Z J : E → ℝ) (x₁ x₂ : E)
    (hJ : Integrable (fun y => K y * J y) μ)
    (hB : Integrable (fun y => K y * ((Z x₂ - Z y) * J y)) μ)
    {κ d t M H Hᵥ HZ NJ NB : ℝ} (hd : 0 < d)
    (hv₁ : |v x₁| ≤ M) (hv₂ : |v x₂| ≤ M)
    (hH : |(v x₁ + Z x₁) - (v x₂ + Z x₂)| ≤ H * d ^ (1 - 2 * κ))
    (hv : |v x₁ - v x₂| ≤ Hᵥ * d ^ (1 / 2 - 3 * κ))
    (hZ : |Z x₁ - Z x₂| ≤ HZ * d ^ (1 / 2 - 3 * κ))
    (hj : |∫ y, K y * J y ∂μ| ≤ NJ * t ^ (-(1 / 2) - κ))
    (hb : |∫ y, K y * ((Z x₂ - Z y) * J y) ∂μ| ≤ NB * t ^ (-4 * κ)) :
    |∫ y, K y * (firstProductGerm v Z J x₁ y - firstProductGerm v Z J x₂ y) ∂μ| ≤
      2 * M * H * NJ * d ^ (1 - 2 * κ) * t ^ (-(1 / 2) - κ) +
      Hᵥ * HZ * NJ * d ^ (1 - 6 * κ) * t ^ (-(1 / 2) - κ) +
      2 * Hᵥ * NB * d ^ (1 / 2 - 3 * κ) * t ^ (-4 * κ) := by
  have hpow : d ^ (1 - 6 * κ) = d ^ (1 / 2 - 3 * κ) * d ^ (1 / 2 - 3 * κ) := by
    rw [← Real.rpow_add hd]
    congr 1
    ring
  convert firstProductGerm_tested_increment_bound μ K v Z J x₁ x₂ hJ hB
    hv₁ hv₂ hH hv hZ hj hb using 1
  rw [hpow]
  ring

end GlobalPhi43.MW20

end
