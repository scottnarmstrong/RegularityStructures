/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Semigroup.Pairing.Basic

/-!
# Pairing with a test function centred away from the base point

For `Λ` of local order `γ` at `x` (exponents `A`), and `h` smooth, vanishing outside the parabolic
ball of radius `lam ∈ (0, 2]`, the pairing with the reflected function `z ↦ h (c - z)` (supported in
the `lam`-ball about `c`) satisfies

  `|⟨Λ, h (c - ·)⟩| ≤ C ∑_{a ∈ A} κ_a lam^a (lam + d(c, x))^{γ - a} (B₀ + B₁)`,

`κ_a = (1 + 4/(a+4)) 2^{-a}`, `∫ |h| ≤ B₀`, `∫ |L h| ≤ B₁ lam^{-4}` (`abs_pairing_reflect_le_centre`).
The proof is `abs_pairing_le_of_time` with radius `R = lam + d(c, x)` (using
`d(z, x) ≤ d(z, c) + d(c, x)`) and time `T = (lam/2)^4`; the factor `2^{-a}` and the allowed range
`lam ≤ 2` come from `T ≤ 1`.  Source: [Hai14, proof of Lemma 5.18 and Lemma 5.19].
-/

public section

open MeasureTheory Set

namespace RegularityStructures

/-- The constant `κ_a = (1 + 4/(a+4)) 2^{-a}`. -/
@[expose] noncomputable def pairingWeight (a : ℝ) : ℝ := (1 + 4 / (a + 4)) * (2 : ℝ) ^ (-a)

theorem pairingWeight_nonneg {a : ℝ} (ha : -4 < a) : 0 ≤ pairingWeight a := by
  have : 0 < a + 4 := by linarith
  exact mul_nonneg (by positivity) (Real.rpow_nonneg (by norm_num) _)

theorem timeTerm_eq {lam a : ℝ} (hlam : 0 < lam) :
    (((lam / 2) ^ (4 : ℝ)) ^ (a / 4)) = (lam / 2) ^ a := by
  rw [← Real.rpow_mul (by positivity)]
  congr 1; ring

theorem incrTerm_eq {lam a : ℝ} (hlam : 0 < lam) (ha : -4 < a) :
    (((lam / 2) ^ (4 : ℝ)) ^ (a / 4 + 1) / (a / 4 + 1)) * lam ^ (-(4 : ℝ)) =
      (lam / 2) ^ a * ((1 / 16) * (4 / (a + 4))) := by
  have hT : (0 : ℝ) < (lam / 2) ^ (4 : ℝ) := by positivity
  have h4 : (lam / 2) ^ (4 : ℝ) = lam ^ 4 / 16 := by
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, div_pow]; norm_num
  have hl : lam ^ (-(4 : ℝ)) = (lam ^ 4)⁻¹ := by
    rw [show (-(4 : ℝ)) = -((4 : ℕ) : ℝ) by norm_num, Real.rpow_neg hlam.le, Real.rpow_natCast]
  have hpos : 0 < a + 4 := by linarith
  rw [Real.rpow_add_one hT.ne', timeTerm_eq hlam, hl, h4]
  have : a / 4 + 1 = (a + 4) / 4 := by ring
  rw [this]
  field_simp

theorem alg_term_le {C P B₀ B₁ v : ℝ} (hC : 0 ≤ C) (hP : 0 ≤ P) (h0 : 0 ≤ B₀) (h1 : 0 ≤ B₁)
    (hv : 0 ≤ v) :
    C * P * B₀ + C * B₁ * (P * ((1 / 16) * v)) ≤ C * ((1 + v) * P) * (B₀ + B₁) := by
  have : C * ((1 + v) * P) * (B₀ + B₁) - (C * P * B₀ + C * B₁ * (P * ((1 / 16) * v))) =
      C * P * (B₁ + v * B₀ + (15 / 16) * v * B₁) := by ring
  have h2 : 0 ≤ C * P * (B₁ + v * B₀ + (15 / 16) * v * B₁) := by positivity
  linarith

end RegularityStructures

end
