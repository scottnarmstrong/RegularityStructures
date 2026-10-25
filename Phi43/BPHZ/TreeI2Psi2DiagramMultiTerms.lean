/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI2Psi2DiagramMultiTriple

/-!
# The monomials of the difference bound for `I(Ψ²) Ψ²`

Throughout `θ ∈ (0, 1/8]`, `δ ∈ (0, 1/4]`, `r = s(y - x)`, `r' = s(y' - x)`, `d = s(y - y')`,
`η = 2θ + δ`, and `F = i2Psi2DiffF θ δ r r' d`.  Each monomial of the second difference of the
chaos kernels is a product of four covariance weights, one of which has its exponent raised by `2θ`
(`TreeI2Psi2DifferencePointwise`).  Its diagram integral is bounded by `C B² F`:

* `i2Psi2LintBound_diff_sq_inner`, `_sq_outer`: `s(w' - w)^(-(2+2θ)) d^(-2)`, `s(w' - w)^(-2)
  d^(-(2+2θ))`;
* `i2Psi2LintBound_diff_prod_left`, `_prod_right`: the product pairings with a raised exponent;
* `i2Psi2LintBound_diff_cross_inner`: the cross pairing with a raised exponent among the three
  integrated weights, times `d^(-1)`;
* `i2Psi2LintBound_diff_cross_outer`: the cross pairing times `d^(-(1+2θ))`.
-/

public section

open MeasureTheory

namespace RegularityStructures

theorem i2Psi2DiffF_ge_one {θ δ r r' d : ℝ} (hr : 0 < r) (hr' : 0 < r') (hd : 0 < d) :
    d ^ (-(2 * θ + δ)) ≤ i2Psi2DiffF θ δ r r' d := by
  obtain ⟨h1, h2, h3, h4⟩ := i2Psi2DiffF_parts_nonneg (θ := θ) (δ := δ) hr hr' hd
  unfold i2Psi2DiffF; linarith

theorem i2Psi2DiffF_ge_two {θ δ r r' d : ℝ} (hr : 0 < r) (hr' : 0 < r') (hd : 0 < d) :
    d ^ (-(2 : ℝ)) * (r ^ (2 - (2 * θ + δ)) + r' ^ (2 - (2 * θ + δ))) ≤
      i2Psi2DiffF θ δ r r' d := by
  obtain ⟨h1, h2, h3, h4⟩ := i2Psi2DiffF_parts_nonneg (θ := θ) (δ := δ) hr hr' hd
  unfold i2Psi2DiffF; linarith

theorem i2Psi2DiffF_ge_three {θ δ r r' d : ℝ} (hr : 0 < r) (hr' : 0 < r') (hd : 0 < d) :
    d ^ (-(2 + 2 * θ)) * (r ^ (2 - δ) + r' ^ (2 - δ)) ≤ i2Psi2DiffF θ δ r r' d := by
  obtain ⟨h1, h2, h3, h4⟩ := i2Psi2DiffF_parts_nonneg (θ := θ) (δ := δ) hr hr' hd
  unfold i2Psi2DiffF; linarith

theorem i2Psi2DiffF_ge_four {θ δ r r' d : ℝ} (hr : 0 < r) (hr' : 0 < r') (hd : 0 < d) :
    r ^ (-(2 * θ + δ)) + r' ^ (-(2 * θ + δ)) ≤ i2Psi2DiffF θ δ r r' d := by
  obtain ⟨h1, h2, h3, h4⟩ := i2Psi2DiffF_parts_nonneg (θ := θ) (δ := δ) hr hr' hd
  unfold i2Psi2DiffF; linarith

/-- `d^(-η) + d^(-2) (r^(2-η) + r'^(2-η)) + r^(-η) ≤ F`. -/
theorem i2Psi2DiffF_ge_pat {θ δ r r' d : ℝ} (hr : 0 < r) (hr' : 0 < r') (hd : 0 < d) :
    d ^ (-(2 : ℝ)) * (r ^ (2 - (2 * θ + δ)) + r' ^ (2 - (2 * θ + δ))) + d ^ (-(2 * θ + δ)) +
      r ^ (-(2 * θ + δ)) ≤ i2Psi2DiffF θ δ r r' d := by
  obtain ⟨h1, h2, h3, h4⟩ := i2Psi2DiffF_parts_nonneg (θ := θ) (δ := δ) hr hr' hd
  have := Real.rpow_nonneg hr'.le (-(2 * θ + δ))
  unfold i2Psi2DiffF; linarith

/-- The same with `r` and `r'` exchanged. -/
theorem i2Psi2DiffF_ge_pat' {θ δ r r' d : ℝ} (hr : 0 < r) (hr' : 0 < r') (hd : 0 < d) :
    d ^ (-(2 : ℝ)) * (r' ^ (2 - (2 * θ + δ)) + r ^ (2 - (2 * θ + δ))) + d ^ (-(2 * θ + δ)) +
      r' ^ (-(2 * θ + δ)) ≤ i2Psi2DiffF θ δ r r' d := by
  obtain ⟨h1, h2, h3, h4⟩ := i2Psi2DiffF_parts_nonneg (θ := θ) (δ := δ) hr hr' hd
  have := Real.rpow_nonneg hr.le (-(2 * θ + δ))
  unfold i2Psi2DiffF; linarith

/-- **Monomial `s(w' - w)^(-(2+2θ)) d^(-2)`.** -/
theorem i2Psi2LintBound_diff_sq_inner {θ δ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1 / 8) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1 / 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {K : SpaceTime → ℝ} {B : ℝ}, i2Psi2KernelHyp K B →
      ∀ x y y' g₁ h : SpaceTime, i2Psi2PointCfg x y y' →
        i2Psi2LintBound volume (fun q => i2Psi2Triple K x y y' g₁ h 0 (2 + 2 * θ) 0 q *
          torusParabolicSize (y - y') ^ (-(2 : ℝ)))
          (C * B ^ 2 * i2Psi2DiffF θ δ (torusParabolicSize (y - x)) (torusParabolicSize (y' - x))
            (torusParabolicSize (y - y'))) := by
  obtain ⟨C0, hC0, h0⟩ := i2Psi2LintBound_diag_sq (γ := 1 - θ - δ / 2) (γ' := 1 - θ - δ / 2)
    (e := 2 + 2 * θ) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    (by linarith) (by linarith)
  refine ⟨C0, hC0, ?_⟩
  intro K B hK x y y' g₁ h hc
  obtain ⟨hr, hr1, hr', hr1', hd⟩ := id hc
  obtain ⟨hxy, hxy'⟩ := hc.time_le
  have hB := hK.1
  have hb := (h0 hK x y y' hxy hxy').const_mul (c := torusParabolicSize (y - y') ^ (-(2 : ℝ)))
    (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)
  refine hb.mono (fun q => ?_) ?_
  · unfold i2Psi2Triple
    simp only [neg_zero, Real.rpow_zero, one_mul, mul_one]
    exact le_of_eq (by ring)
  · have amgm := rpow_mul_rpow_le_add_two hr hr' (g := 1 - θ - δ / 2)
    have e2 : 2 * (1 - θ - δ / 2) = 2 - (2 * θ + δ) := by ring
    rw [e2] at amgm
    have hF := i2Psi2DiffF_ge_two (θ := θ) (δ := δ) hr hr' hd
    have hCB : 0 ≤ C0 * B ^ 2 := by positivity
    have nd : 0 ≤ torusParabolicSize (y - y') ^ (-(2 : ℝ)) := Real.rpow_nonneg hd.le _
    calc torusParabolicSize (y - y') ^ (-(2 : ℝ)) * (C0 * B ^ 2 * torusParabolicSize (y - x) ^
          (1 - θ - δ / 2) * torusParabolicSize (y' - x) ^ (1 - θ - δ / 2))
        = C0 * B ^ 2 * (torusParabolicSize (y - y') ^ (-(2 : ℝ)) *
          (torusParabolicSize (y - x) ^ (1 - θ - δ / 2) *
            torusParabolicSize (y' - x) ^ (1 - θ - δ / 2))) := by ring
      _ ≤ C0 * B ^ 2 * (torusParabolicSize (y - y') ^ (-(2 : ℝ)) *
          (torusParabolicSize (y - x) ^ (2 - (2 * θ + δ)) +
            torusParabolicSize (y' - x) ^ (2 - (2 * θ + δ)))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left amgm nd) hCB
      _ ≤ _ := mul_le_mul_of_nonneg_left hF hCB

/-- **Monomial `s(w' - w)^(-2) d^(-(2+2θ))`.** -/
theorem i2Psi2LintBound_diff_sq_outer {θ δ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1 / 8) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1 / 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {K : SpaceTime → ℝ} {B : ℝ}, i2Psi2KernelHyp K B →
      ∀ x y y' g₁ h : SpaceTime, i2Psi2PointCfg x y y' →
        i2Psi2LintBound volume (fun q => i2Psi2Triple K x y y' g₁ h 0 2 0 q *
          torusParabolicSize (y - y') ^ (-(2 + 2 * θ)))
          (C * B ^ 2 * i2Psi2DiffF θ δ (torusParabolicSize (y - x)) (torusParabolicSize (y' - x))
            (torusParabolicSize (y - y'))) := by
  obtain ⟨C0, hC0, h0⟩ := i2Psi2LintBound_diag_sq (γ := 1 - δ / 2) (γ' := 1 - δ / 2)
    (e := 2) (by linarith) (by linarith) (by linarith) (by linarith) (by norm_num)
    (by linarith) (by linarith)
  refine ⟨C0, hC0, ?_⟩
  intro K B hK x y y' g₁ h hc
  obtain ⟨hr, hr1, hr', hr1', hd⟩ := id hc
  obtain ⟨hxy, hxy'⟩ := hc.time_le
  have hB := hK.1
  have hb := (h0 hK x y y' hxy hxy').const_mul
    (c := torusParabolicSize (y - y') ^ (-(2 + 2 * θ)))
    (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)
  refine hb.mono (fun q => ?_) ?_
  · unfold i2Psi2Triple
    simp only [neg_zero, Real.rpow_zero, one_mul, mul_one]
    exact le_of_eq (by ring)
  · have amgm := rpow_mul_rpow_le_add_two hr hr' (g := 1 - δ / 2)
    have e2 : 2 * (1 - δ / 2) = 2 - δ := by ring
    rw [e2] at amgm
    have hF := i2Psi2DiffF_ge_three (θ := θ) (δ := δ) hr hr' hd
    have hCB : 0 ≤ C0 * B ^ 2 := by positivity
    have nd : 0 ≤ torusParabolicSize (y - y') ^ (-(2 + 2 * θ)) := Real.rpow_nonneg hd.le _
    calc torusParabolicSize (y - y') ^ (-(2 + 2 * θ)) * (C0 * B ^ 2 *
          torusParabolicSize (y - x) ^ (1 - δ / 2) * torusParabolicSize (y' - x) ^ (1 - δ / 2))
        = C0 * B ^ 2 * (torusParabolicSize (y - y') ^ (-(2 + 2 * θ)) *
          (torusParabolicSize (y - x) ^ (1 - δ / 2) * torusParabolicSize (y' - x) ^ (1 - δ / 2))) :=
          by ring
      _ ≤ C0 * B ^ 2 * (torusParabolicSize (y - y') ^ (-(2 + 2 * θ)) *
          (torusParabolicSize (y - x) ^ (2 - δ) + torusParabolicSize (y' - x) ^ (2 - δ))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left amgm nd) hCB
      _ ≤ _ := mul_le_mul_of_nonneg_left hF hCB

end RegularityStructures

end
