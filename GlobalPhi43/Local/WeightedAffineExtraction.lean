/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import GlobalPhi43.Local.WeightedAffineError

/-! Extraction from the actual weighted affine-error supremum, with the
exact d^gamma/R^gamma factor and no finite-error premise. -/
public noncomputable section

namespace GlobalPhi43.Local

open RegularityStructures MW20 Set
open scoped ENNReal

theorem weightedPastAffineError_bound (U : GermPoint → ℝ) {r d₀ θ γ d R F : ℝ}
    (hnorm : weightedPastAffineError U r d₀ θ γ ≤ ENNReal.ofReal F)
    (hd : d ∈ Ioc (0 : ℝ) d₀) {x : ParabolicSpace} (hx : x ∈ cylinderInterior r d)
    (hR : R ∈ Ioc (0 : ℝ) (θ * d)) :
    pastAffineError (fun y => U (x, y)) x R ≤ ENNReal.ofReal ((F / d ^ γ) * R ^ γ) := by
  have hall : ∀ d ∈ Ioc (0 : ℝ) d₀, ∀ x ∈ cylinderInterior r d,
      ∀ R ∈ Ioc (0 : ℝ) (θ * d), ENNReal.ofReal (d ^ γ / R ^ γ) *
        pastAffineError (fun y => U (x, y)) x R ≤ ENNReal.ofReal F := by
    simpa only [weightedPastAffineError, iSup_le_iff] using hnorm
  have hh := hall d hd x hx R hR
  let a := d ^ γ / R ^ γ
  have ha : 0 < a := div_pos (Real.rpow_pos_of_pos hd.1 _) (Real.rpow_pos_of_pos hR.1 _)
  have hi : 0 ≤ 1 / a := by positivity
  have hc : (1 / a) * a = 1 := by field_simp
  have hc' : ENNReal.ofReal (1 / a) * ENNReal.ofReal a = 1 := by
    rw [← ENNReal.ofReal_mul hi, hc]
    norm_num
  have hmul := mul_le_mul (le_rfl : ENNReal.ofReal (1 / a) ≤ ENNReal.ofReal (1 / a)) hh
    (by positivity) (by positivity)
  have he : pastAffineError (fun y => U (x, y)) x R ≤
      ENNReal.ofReal (1 / a) * ENNReal.ofReal F := by
    change ENNReal.ofReal (1 / a) * (ENNReal.ofReal a *
      pastAffineError (fun y => U (x, y)) x R) ≤ ENNReal.ofReal (1 / a) * ENNReal.ofReal F at hmul
    simpa only [← mul_assoc, hc', one_mul] using hmul
  have hscalar : (1 / a) * F = (F / d ^ γ) * R ^ γ := by
    dsimp [a]
    field_simp
  simpa only [← ENNReal.ofReal_mul hi, hscalar] using he

/-- The finite supremum supplies its own literal real allowance. -/
theorem weightedPastAffineError_bound_toReal (U : GermPoint → ℝ) {r d₀ θ γ d R : ℝ}
    (hfinite : weightedPastAffineError U r d₀ θ γ ≠ ⊤)
    (hd : d ∈ Ioc (0 : ℝ) d₀) {x : ParabolicSpace} (hx : x ∈ cylinderInterior r d)
    (hR : R ∈ Ioc (0 : ℝ) (θ * d)) :
    pastAffineError (fun y => U (x, y)) x R ≤
      ENNReal.ofReal (((weightedPastAffineError U r d₀ θ γ).toReal / d ^ γ) * R ^ γ) := by
  apply weightedPastAffineError_bound U _ hd hx hR
  rw [ENNReal.ofReal_toReal hfinite]

end GlobalPhi43.Local
